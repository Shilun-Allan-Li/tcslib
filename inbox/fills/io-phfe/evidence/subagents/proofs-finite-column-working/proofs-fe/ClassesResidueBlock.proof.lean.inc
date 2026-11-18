/-- Each coordinate of total residue decoding reads its canonical row-major bit
block and reduces that block's natural value modulo p. This is technical wire-
representation glue, valid for every word without a canonicality or width bound.

**Proof sketch.** Read decodeResidues_apply. Identify its drop/take block with the
finite list of the row's width bit coordinates, using the published list element,
length, and finite-product coordinate equations. Then transport the list equality
through listToNat and the residue cast; no range rejection is introduced. -/
theorem decodeResidues_block (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) (i : Fin count) :
    decodeResidues p count width word i =
      (listToNat (List.ofFn (fun j : Fin width => word (finProdFinEquiv (i, j)))) :
        ZMod (p : ℕ)) := by
  rw [decodeResidues_apply]
  apply congrArg (fun bits : List Bool => (listToNat bits : ZMod (p : ℕ)))
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_ofFn]
    apply Nat.min_eq_left
    have hcut := Nat.mul_le_mul_right width (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hcut
    omega
  · intro j hj hk
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    apply congrArg word
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]
