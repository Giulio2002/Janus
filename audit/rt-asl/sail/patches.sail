default Order dec
$include <prelude.sail>
$include <real.sail>

/* Probes of JanusASL's Sail Lean-backend fixes (docs/ASL.md, Sail patches; docs/AUDIT-ASL.md A5).
   The same functions are run by Sail's C backend and by the (patched) Lean backend. */

val dummy0 : unit -> int
function dummy0() = 0

register R : bits(8)

/* fix 5: an effectful integer let whose first branch is non-negative */
val asl_int_like : bool -> int
function asl_int_like(u) = {
  let r : int = if u then unsigned(R) else signed(R);
  r
}

val probe : bits(8) -> int
function probe(v) = {
  R = v;
  let x = asl_int_like(true);
  let y = asl_int_like(false);
  x + 1000 * y
}

/* fix 1: one-bit vectors */
val onebit : bits(8) -> int
function onebit(v) = {
  let b : bits(1) = [v[3]];
  let c : bits(2) = [v[7], v[0]];
  unsigned(b) * 10 + unsigned(c)
}

/* fix 4: the vector-concat assignment as a statement, in an if and in a loop */
val va : bits(8) -> int
function va(v) = {
  var hi : bits(4) = 0x0;
  var lo : bits(4) = 0x0;
  { (hi @ lo) = v; };
  unsigned(hi) * 16 + unsigned(lo)
}

val vd : bits(8) -> int
function vd(v) = {
  var hi : bits(4) = 0x0;
  var lo : bits(4) = 0x0;
  (hi @ lo) = v;
  unsigned(hi) * 16 + unsigned(lo)
}

val vg : bits(8) -> int
function vg(v) = {
  var hi : bits(4) = 0x0;
  var lo : bits(4) = 0x0;
  if v[0] == bitone then { (hi @ lo) = v; } else { hi = 0xf };
  unsigned(hi) * 16 + unsigned(lo)
}

val vh : bits(8) -> int
function vh(v) = {
  var hi : bits(4) = 0x0;
  var lo : bits(4) = 0x0;
  foreach (i from 0 to 1) { (hi @ lo) = v; hi = hi + 1 };
  unsigned(hi) * 16 + unsigned(lo)
}

/* assignments in an if / match bound by let (handled) */
val vc : bits(8) -> int
function vc(v) = {
  var hi : bits(4) = 0x0;
  let t : int = if v[0] == bitone then { hi = v[7 .. 4]; 1 } else 0;
  t * 1000 + unsigned(hi)
}

val ve : bits(8) -> int
function ve(v) = {
  var hi : bits(4) = 0x0;
  let t : int = match v[1 .. 0] { 0b00 => { hi = v[7 .. 4]; 1 }, _ => 2 };
  t * 1000 + unsigned(hi)
}

/* fix 6: exact reals */
val rtz : (int, int) -> int
function rtz(a, b) = {
  let r : real = div_real(to_real(a), to_real(b));
  if lt_real(r, to_real(0)) then ceil(r) else floor(r)
}

val rpow : (int, int) -> int
function rpow(a, n) = floor(mult_real(pow_real(to_real(a), n), to_real(1000000)))

/* C2 (open, latent): a let/var whose initializer is a block that assigns outer variables.
   The Lean backend drops the assignments (C: the updated values; Lean: the old ones). */
val vb : bits(8) -> int
function vb(v) = {
  var hi : bits(4) = 0x0;
  let t : int = { hi = v[7 .. 4]; unsigned(hi) };
  t * 1000 + unsigned(hi)
}

val vf : bits(8) -> int
function vf(v) = {
  var hi : bits(4) = 0x0;
  var t : int = { hi = v[7 .. 4]; 3 };
  t * 1000 + unsigned(hi)
}

val vcat : bits(8) -> int
function vcat(v) = {
  var hi : bits(4) = 0x0;
  var lo : bits(4) = 0x0;
  let t : int = { (hi @ lo) = v; unsigned(hi) };
  t * 1000 + unsigned(hi) * 16 + unsigned(lo)
}

/* The sqrt_real replacement (JanusASL/sail/fakereal_sqrt.py; run.sh applies it to this probe's
   FakeReal.lean as scripts/asl.sh gen does): floor(sqrt(a/b) * 2^80), Lean against C (GMP Newton
   iteration to 10^-30). */
val rsq : (int, int) -> int
function rsq(a, b) = floor(mult_real(sqrt(div_real(to_real(a), to_real(b))), pow_real(to_real(2), 80)))

/* The integer_update_subrange replacement (JanusASL/sail/sail_int_fix.py; run.sh applies it to
   this probe's Lean output as scripts/asl.sh gen does): bit 0, bits 7..4 and bits 63..60 of an
   integer (two's complement, any sign and size) replaced, Lean against C. */
/* sail-arm's prelude.sail:183-184, verbatim */
val integer_update_subrange : forall 'm 'o, 0 <= 'o <= 'm. (int, int('m), int('o), bits('m - 'o + 1)) -> int
function integer_update_subrange(i, hi, lo, x) = set_slice_int(hi - lo + 1, i, lo, x)

val ius : (int, int) -> int
function ius(k, i) =
  if k == 0 then integer_update_subrange(i, 0, 0, 0b1)
  else if k == 1 then integer_update_subrange(i, 7, 4, 0xA)
  else integer_update_subrange(i, 63, 60, 0x5)
