theorem auxCount_add_one (l d : ℕ) : auxCount l d + 1 = nodeCount l d := by
  rw [auxCount_eq, nodeCount_eq, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero]
  exact Nat.add_comm _ _
