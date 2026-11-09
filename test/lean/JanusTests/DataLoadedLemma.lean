import Janus

/-!
# `Program.DataLoaded_of_dataSegByte` on a small program

The witness memory reads the data as `dataSegByte` does; `DataLoaded` follows from disjointness, the byte bound, the read-only regions and one
statement per address. Overlapping objects are refused by the disjointness premise (the lemma is false for them).
-/

open Janus

def tp : Program :=
  { segments := [], stubs := [], exitAddr := 0,
    data := [⟨"a", 0x1000, [1, 2, 3]⟩, ⟨"b", 0x2000, [255, 0]⟩] }

def tmem : Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dataSegByte tp.data a).getD 0), [⟨0x1000, 3, false⟩, ⟨0x2000, 2, false⟩]⟩

theorem tp_loaded : tp.DataLoaded tmem :=
  Program.DataLoaded_of_dataSegByte (by unfold DataSegsDisjoint; decide +kernel) (by decide +kernel) (by decide +kernel)
    fun a n h => by
      show (BitVec.ofNat 8 ((dataSegByte tp.data a).getD 0)).toNat = n % 256
      rw [h]; simp

-- the byte of a segment is the segment's own byte, and an address outside every segment reads nothing
example : dataSegByte tp.data 0x1001 = some 2 := by decide +kernel
example : dataSegByte tp.data 0x2001 = some 0 := by decide +kernel
example : dataSegByte tp.data 0x1500 = none := by decide +kernel
