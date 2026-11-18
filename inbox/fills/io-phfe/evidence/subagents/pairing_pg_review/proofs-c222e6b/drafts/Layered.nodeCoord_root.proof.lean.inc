theorem nodeCoord_root (l d : ℕ) : (nodeCoord l d (root l d)).val = 0 := by
  rw [nodeCoord_eq, root_eq]
  change (finSigmaFinEquiv
    (⟨⟨0, Nat.zero_lt_succ d⟩, tupleCoord l 0 Fin.elim0⟩ :
      Σ k : Fin (d + 1), Fin ((l + 1) ^ k.val))).val = 0
  simp only [finSigmaFinEquiv_apply, tupleCoord_eq, finFunctionFinEquiv_apply,
    Fin.sum_univ_zero, zero_add]
