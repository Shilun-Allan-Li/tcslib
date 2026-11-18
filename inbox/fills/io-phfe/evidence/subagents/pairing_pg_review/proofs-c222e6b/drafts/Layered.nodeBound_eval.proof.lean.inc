theorem nodeBound_eval (l : PolyExpr) (d kappa : ℕ) :
    (nodeBound l d).eval kappa = nodeCount (l.eval kappa) d := by
  induction d with
  | zero =>
      simp only [nodeBound_zero, nodeCount_eq, Fin.sum_univ_one, Fin.val_zero, pow_zero]
      rfl
  | succ d ih =>
      rw [nodeBound_succ]
      change (nodeBound l d).eval kappa + (l.eval kappa + 1) ^ (d + 1) =
        nodeCount (l.eval kappa) (d + 1)
      rw [ih]
      simpa only [nodeCount_eq, Fin.coe_castSucc, Fin.val_last] using
        (Fin.sum_univ_castSucc
          (fun k : Fin (d + 2) => (l.eval kappa + 1) ^ k.val)).symm
