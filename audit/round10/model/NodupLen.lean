theorem nodup_len_ge : ∀ (N : Nat) (l : List (BitVec 64)), N ≤ 2 ^ 64 → l.Nodup →
    (∀ i, i < N → BitVec.ofNat 64 i ∈ l) → N ≤ l.length
  | 0, _, _, _, _ => Nat.zero_le _
  | N + 1, l, hN, hnd, hall => by
    have hx := hall N (by omega)
    have hlen := List.length_erase_of_mem hx
    have hnd' : (l.erase (BitVec.ofNat 64 N)).Nodup := hnd.erase _
    have ih := nodup_len_ge N (l.erase (BitVec.ofNat 64 N)) (by omega) hnd' (fun i hi => by
      rw [List.Nodup.mem_erase_iff hnd]
      refine ⟨fun h => ?_, hall i (by omega)⟩
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega)
    have : 0 < l.length := List.length_pos_of_mem hx
    omega
