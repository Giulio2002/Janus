import Janus.Contracts.Libc
import Janus.Amd64.FFI

/-!
# libc contracts, `setjmp`/`longjmp`, and the TLS block (amd64)

The x86-64 counterpart of `Janus.Contracts.Libc` (read that module first): the same functions,
the same memory model of the C heap (`heapAlloc`, `heapFree`, the ghost block records) and the
same abstract `jmp_buf`, over the System V calling convention. A PLT stub (`.plt.sec`:
`ENDBR64; [BND] JMP [RIP+d]`, or `.plt`: `JMP [RIP+d]; PUSH; JMP`, its slot the target of an
`R_X86_64_JUMP_SLOT` relocation) is reached by `CALL`, so at the stub `[RSP]` holds the return
address; the call returns there with `RSP + 8`, `RBX RBP R12–R15`, a clear direction flag, the
`MXCSR` control bits and the x87 control word kept (`CReturn`), on the same thread (`FS`).
Arguments are in `RDI RSI RDX RCX`, the result in `RAX`.

TLS (x86-64 ELF TLS ABI, variant II): `FS` points at the thread control block, whose first
word is its own address (`TLSBlock.self`: the general-dynamic code relaxed by the linker reads
`%fs:0`); the executable's TLS block lies just below, at `FS − roundUp(p_memsz, p_align)`.
-/

namespace Janus.Contracts.LibcAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Amd64.CABI Janus.Amd64.FFI
open Janus.Contracts.Libc (libcStack copyMem setMem CStr cstrBytes lexCmp heapAlloc heapFree
  heapToken HeapBlock Fresh JmpCtx jmpBufSize)

/-- What every libc call needs: the stack window (`libcStack` writable bytes below `RSP`, and
the return address). -/
def LibcCall (s : State) : Prop := CStack s libcStack 8

/-- The call from `s` (at the stub: `[RSP]` the return address) returned in `s'` with `RAX`
satisfying `ret` and memory `m` outside the stack bytes below `RSP`: at the return address,
with the System V callee-saved state (`CReturn`) on the same thread (`FS`). -/
structure LibcRet (s s' : State) (m : Memory) (ret : W64 → Prop) : Prop where
  rip : s'.rip = retAddrOf s
  rax : ret (s'.regs 0)
  cret : CReturn s s'
  fs : s'.fsBase = s.fsBase
  regions : s'.mem.regions = m.regions
  mem : MemFrame m s'.mem [((s.regs 4).toNat - libcStack, (s.regs 4).toNat)]

/-- One external function of a contract (as `Janus.Contracts.Libc.Spec`, over amd64 states). -/
structure Spec where
  name : String
  safe : State → Prop
  next : State → State → Prop

def ofSpecs (l : List Spec) : Contract where
  safe f s := ∃ sp ∈ l, sp.name = f ∧ sp.safe s
  next f s s' := ∃ sp ∈ l, sp.name = f ∧ sp.safe s ∧ sp.next s s'

theorem ofSpecs_safe {l : List Spec} {sp : Spec} (hm : sp ∈ l) {s : State} (h : sp.safe s) :
    (ofSpecs l).safe sp.name s := ⟨sp, hm, rfl, h⟩

theorem ofSpecs_next {l : List Spec} {sp : Spec} (hm : sp ∈ l)
    (hu : ∀ sp' ∈ l, sp'.name = sp.name → sp' = sp) {s s' : State}
    (h : (ofSpecs l).next sp.name s s') : sp.next s s' := by
  obtain ⟨sp', hm', hn, -, hx⟩ := h
  rw [hu sp' hm' hn] at hx; exact hx

theorem ofSpecs_total {l : List Spec} (h : ∀ sp ∈ l, ∀ s, sp.safe s → ∃ s', sp.next s s') :
    (ofSpecs l).Total := fun _ s ⟨sp, hm, hn, hs⟩ =>
  let ⟨s', h'⟩ := h sp hm s hs; ⟨s', sp, hm, hn, hs, h'⟩

/-- `n` bytes at `ptr` readable (`w = false`) or writable, below `2^48`. -/
def Buffer (s : State) (ptr : W64) (n : Nat) (w : Bool) : Prop :=
  ptr.toNat + n ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat n w = true

def memcpySpec (name : String := "memcpy@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 7) (s.regs 2).toNat true ∧
    Buffer s (s.regs 6) (s.regs 2).toNat false ∧
    ((s.regs 7).toNat + (s.regs 2).toNat ≤ (s.regs 6).toNat ∨
      (s.regs 6).toNat + (s.regs 2).toNat ≤ (s.regs 7).toNat)
  next s s' := LibcRet s s' (copyMem s.mem (s.regs 7).toNat (s.regs 6).toNat (s.regs 2).toNat)
    (· = s.regs 7)

def memcpyChkSpec : Spec where
  name := "__memcpy_chk@plt"
  safe s := (memcpySpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 1).toNat
  next s s' := (memcpySpec).next s s'

def memmoveSpec (name : String := "memmove@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 7) (s.regs 2).toNat true ∧
    Buffer s (s.regs 6) (s.regs 2).toNat false
  next s s' := LibcRet s s' (copyMem s.mem (s.regs 7).toNat (s.regs 6).toNat (s.regs 2).toNat)
    (· = s.regs 7)

def memmoveChkSpec : Spec where
  name := "__memmove_chk@plt"
  safe s := (memmoveSpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 1).toNat
  next s s' := (memmoveSpec).next s s'

def memsetSpec (name : String := "memset@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 7) (s.regs 2).toNat true
  next s s' := LibcRet s s' (setMem s.mem (s.regs 7).toNat ((s.regs 6).toNat % 256) (s.regs 2).toNat)
    (· = s.regs 7)

def memsetChkSpec : Spec where
  name := "__memset_chk@plt"
  safe s := (memsetSpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 1).toNat
  next s s' := (memsetSpec).next s s'

def strlenSpec : Spec where
  name := "strlen@plt"
  safe s := LibcCall s ∧ ∃ n, CStr s.mem (s.regs 7).toNat n
  next s s' := ∃ n, CStr s.mem (s.regs 7).toNat n ∧ LibcRet s s' s.mem (· = BitVec.ofNat 64 n)

def strcmpSpec : Spec where
  name := "strcmp@plt"
  safe s := LibcCall s ∧ (∃ n, CStr s.mem (s.regs 7).toNat n) ∧ ∃ n, CStr s.mem (s.regs 6).toNat n
  next s s' := ∃ na nb, CStr s.mem (s.regs 7).toNat na ∧ CStr s.mem (s.regs 6).toNat nb ∧
    LibcRet s s' s.mem (Janus.Contracts.Libc.CmpResult (lexCmp (cstrBytes s.mem (s.regs 7).toNat na)
      (cstrBytes s.mem (s.regs 6).toNat nb)))

/-- `malloc(n)`: null, or a 16-aligned (glibc's `MALLOC_ALIGNMENT` on x86-64) fresh block. -/
def mallocSpec : Spec where
  name := "malloc@plt"
  safe s := LibcCall s
  next s s' := LibcRet s s' s.mem (· = 0) ∨
    ∃ p junk, p ≠ 0 ∧ p % 16 = 0 ∧ Fresh s.mem p (s.regs 7).toNat ∧
      LibcRet s s' (heapAlloc s.mem p (s.regs 7).toNat junk) (· = BitVec.ofNat 64 p)

def freeSpec : Spec where
  name := "free@plt"
  safe s := LibcCall s ∧ (s.regs 7 = 0 ∨ ∃ n, HeapBlock s.mem (s.regs 7).toNat n)
  next s s' := (s.regs 7 = 0 ∧ LibcRet s s' s.mem fun _ => True) ∨
    ∃ n junk, HeapBlock s.mem (s.regs 7).toNat n ∧
      LibcRet s s' (heapFree s.mem (s.regs 7).toNat n junk) fun _ => True

def libcSpecs : List Spec :=
  [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec, strlenSpec,
   strcmpSpec, mallocSpec, freeSpec]

/-- The **trusted** libc contract (glibc on Linux/amd64, called through the PLT). -/
def Libc : Contract := ofSpecs libcSpecs

theorem libcSpecs_unique : ∀ sp ∈ libcSpecs, ∀ sp' ∈ libcSpecs, sp'.name = sp.name → sp' = sp := by
  simp only [libcSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  intro sp hsp sp' hsp' hn
  rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hsp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec,
    memsetChkSpec, strlenSpec, strcmpSpec, mallocSpec, freeSpec] at hn; exact absurd hn (by decide))

theorem libc_call {sp : Spec} (hm : sp ∈ libcSpecs) {S : State} {K : State → Prop}
    (hs : sp.safe S) (hk : ∀ s', sp.next S s' → K s') :
    Libc.safe sp.name S ∧ ∀ s', Libc.next sp.name S s' → K s' :=
  ⟨ofSpecs_safe hm hs, fun s' h =>
    hk s' (ofSpecs_next hm (fun sp' hm' hn => libcSpecs_unique sp hm sp' hm' hn) h)⟩

/-! ## `setjmp` and `longjmp` -/

/-- What `_setjmp` saves (glibc `sysdeps/x86_64/setjmp.S`): `RBX RBP R12–R15`, the caller's
`RSP` after the return (`RSP + 8` at the stub) and the return address. The same abstract
`JmpModel` as on arm64, over this context. -/
structure JmpCtx64 where
  rbx : W64
  rbp : W64
  r12 : W64
  r13 : W64
  r14 : W64
  r15 : W64
  sp : W64
  pc : W64

def jmpCtxOf (s : State) : JmpCtx64 :=
  ⟨s.regs 3, s.regs 5, s.regs 12, s.regs 13, s.regs 14, s.regs 15, s.regs 4 + 8, retAddrOf s⟩

/-- `sizeof(jmp_buf)` on Linux/x86-64 (glibc: 8 saved words, `__mask_was_saved`, padding, the
128-byte signal mask). -/
def jmpBufSize64 : Nat := 200

structure JmpModel64 where
  holds : Memory → Nat → JmpCtx64 → Prop
  unique : ∀ m env c c', holds m env c → holds m env c' → c = c'
  locality : ∀ m m' env c, (∀ i, i < jmpBufSize64 → m'.bytes (env + i) = m.bytes (env + i)) →
    holds m env c → holds m' env c
  store : ∀ (m : Memory) env c, ∃ m' : Memory, m'.regions = m.regions ∧
    (∀ a, a < env ∨ env + jmpBufSize64 ≤ a → m'.bytes a = m.bytes a) ∧ holds m' env c

def setjmpSpec (J : JmpModel64) : Spec where
  name := "_setjmp@plt"
  safe s := LibcCall s ∧ Buffer s (s.regs 7) jmpBufSize64 true ∧
    Outside (s.regs 7).toNat jmpBufSize64 [((s.regs 4).toNat - libcStack, (s.regs 4).toNat + 8)]
  next s s' := ∃ m, m.regions = s.mem.regions ∧
    (∀ a, a < (s.regs 7).toNat ∨ (s.regs 7).toNat + jmpBufSize64 ≤ a → m.bytes a = s.mem.bytes a) ∧
    J.holds m (s.regs 7).toNat (jmpCtxOf s) ∧ LibcRet s s' m (· = 0)

/-- `longjmp(env, v)` resumes the context `c`: a second return from `_setjmp` at `c.pc` with
`c`'s `RSP` and callee-saved registers, `EAX = v` (`1` if `v = 0`; the upper half of `RAX`
zero), a clear direction flag, and the current `MXCSR`, x87 control word, thread and memory. -/
structure LongjmpTo (s s' : State) (c : JmpCtx64) : Prop where
  rip : s'.rip = c.pc
  sp : s'.regs 4 = c.sp
  rbx : s'.regs 3 = c.rbx
  rbp : s'.regs 5 = c.rbp
  r12 : s'.regs 12 = c.r12
  r13 : s'.regs 13 = c.r13
  r14 : s'.regs 14 = c.r14
  r15 : s'.regs 15 = c.r15
  rax : s'.regs 0 = if (s.regs 6).setWidth 32 = 0 then 1 else ((s.regs 6).setWidth 32).setWidth 64
  df : s'.df = false
  mxcsr : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64
  fpucw : s'.fpucw = s.fpucw
  fs : s'.fsBase = s.fsBase
  regions : s'.mem.regions = s.mem.regions
  mem : MemFrame s.mem s'.mem [((s.regs 4).toNat - libcStack, (s.regs 4).toNat)]

def longjmpSpec (J : JmpModel64) (name : String := "longjmp@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ ∃ c, J.holds s.mem (s.regs 7).toNat c
  next s s' := ∃ c, J.holds s.mem (s.regs 7).toNat c ∧ LongjmpTo s s' c

/-- `__longjmp_chk`: only upwards (glibc aborts on a jump to a frame below the current one). -/
def longjmpChkSpec (J : JmpModel64) : Spec where
  name := "__longjmp_chk@plt"
  safe s := LibcCall s ∧ ∃ c, J.holds s.mem (s.regs 7).toNat c ∧ (s.regs 4).toNat ≤ c.sp.toNat
  next s s' := ∃ c, J.holds s.mem (s.regs 7).toNat c ∧ LongjmpTo s s' c

def setJmpSpecs (J : JmpModel64) : List Spec :=
  [setjmpSpec J, longjmpSpec J, longjmpChkSpec J, longjmpSpec J "_longjmp@plt"]

/-- The **trusted** `setjmp`/`longjmp` contract (amd64), for the `jmp_buf` model `J`. -/
def SetJmp (J : JmpModel64) : Contract := ofSpecs (setJmpSpecs J)

theorem setJmpSpecs_unique (J : JmpModel64) :
    ∀ sp ∈ setJmpSpecs J, ∀ sp' ∈ setJmpSpecs J, sp'.name = sp.name → sp' = sp := by
  simp only [setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  intro sp hsp sp' hsp' hn
  rcases hsp with rfl | rfl | rfl | rfl <;> rcases hsp' with rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [setjmpSpec, longjmpSpec, longjmpChkSpec] at hn; exact absurd hn (by decide))

theorem setJmp_call {J : JmpModel64} {sp : Spec} (hm : sp ∈ setJmpSpecs J) {S : State}
    {K : State → Prop} (hs : sp.safe S) (hk : ∀ s', sp.next S s' → K s') :
    (SetJmp J).safe sp.name S ∧ ∀ s', (SetJmp J).next sp.name S s' → K s' :=
  ⟨ofSpecs_safe hm hs, fun s' h =>
    hk s' (ofSpecs_next hm (fun sp' hm' hn => setJmpSpecs_unique J sp hm sp' hm' hn) h)⟩

theorem libc_disjoint_setJmp (J : JmpModel64) : Libc.Disjoint (SetJmp J) := by
  rintro f s s' ⟨sp, hm, rfl, -⟩ ⟨sp', hm', hn, -⟩
  simp only [libcSpecs, setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hm hm'
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hm' with rfl | rfl | rfl | rfl <;>
  (simp only [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec,
    strlenSpec, strcmpSpec, mallocSpec, freeSpec, setjmpSpec, longjmpSpec, longjmpChkSpec] at hn;
   exact absurd hn (by decide))

/-! ## Thread-local storage -/

/-- The **TLS-block contract** (amd64): the executable's TLS block is writable memory just below
`FS`, and the thread control block's first word, at `FS`, is readable and holds `FS` itself. -/
structure TLSBlock (t : TLSImage) (s : State) : Prop where
  base : t.x64Off ≤ s.fsBase.toNat ∧ s.fsBase.toNat + 8 ≤ 2 ^ 48
  block : s.mem.accessible (s.fsBase.toNat - t.x64Off) t.x64Off true = true
  selfAcc : s.mem.accessible s.fsBase.toNat 8 false = true
  self : s.mem.readLE s.fsBase.toNat 8 = s.fsBase.toNat

/-- `__tls_get_addr(ti)` (traditional general dynamic, called through the PLT): `ti` points at a
`tls_index` `{module, offset}`; the call returns the address of that offset in the thread's
block of the module (`block m`, the address glibc's DTV gives; for the executable, module 1,
`FS − x64Off`). It preserves the callee-saved state and memory outside its stack bytes (its
first call for a module of a `dlopen`ed object allocates the block, which this contract does not
cover: `module` names a module whose block exists). -/
def tlsGetAddrSpec (block : Nat → Nat) : Spec where
  name := "__tls_get_addr@plt"
  safe s := LibcCall s ∧ Buffer s (s.regs 7) 16 false
  next s s' := LibcRet s s' s.mem
    (· = BitVec.ofNat 64 (block (s.mem.readLE (s.regs 7).toNat 8) + s.mem.readLE ((s.regs 7).toNat + 8) 8))

/-- The `__tls_get_addr` contract, for the thread's module blocks `block`. -/
def TLSGetAddr (block : Nat → Nat) : Contract := ofSpecs [tlsGetAddrSpec block]

/-- A TLS descriptor's function (x86-64 TLSDESC, `-mtls-dialect=gnu2`: `call *(%rax)` with `RAX`
the descriptor): it returns in `RAX` the variable's offset from `FS` and preserves every other
register (and `DF`, `MXCSR`, the vector registers) and memory outside its stack bytes. -/
def TLSDescFn (p : Janus.Amd64.Program) (f : W64) (desc off : Nat) (stack : Nat) : Prop :=
  f.toNat < 2 ^ 47 ∧
  Summary p f.toNat (fun s => s.regs 0 = BitVec.ofNat 64 desc ∧ CStack s stack 8 ∧
      s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (fun s s' => s'.regs 0 = BitVec.ofNat 64 off ∧ (∀ i, i ≠ 0 → i ≠ 4 → s'.regs i = s.regs i) ∧
      s'.regs 4 = s.regs 4 + 8 ∧ s'.xmm = s.xmm ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
      MemFrame s.mem s'.mem [((s.regs 4).toNat - stack, (s.regs 4).toNat)])

end Janus.Contracts.LibcAmd64
