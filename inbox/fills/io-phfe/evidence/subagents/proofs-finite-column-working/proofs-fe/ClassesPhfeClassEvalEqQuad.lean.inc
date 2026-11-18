/-- The PHFE class embeds into the quadratic class by the identity on coefficient
words and duplication of the private word. [GJLS21, §9; Wee20, §3, p.6].

**Proof sketch.** The duplicated word decodes to two copies of the same residue
vector, by the total block-decoding reader and the published finite-sum/product
coordinate equations. The typed evaluations then agree by phfeEval_eq. -/
theorem phfeClass_eval_eq_quad (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (f : Fin ((tensorFnLen l (.mul n n) w d).eval kappa) → Bool)
    (x : Fin (l.eval kappa * w.eval kappa) → Bool)
    (y : Fin (n.eval kappa * w.eval kappa) → Bool) :
    (phfeClass l n w d).eval kappa p f x y =
      (quadClass l n n w d).eval kappa p f x
        (duplicatePrivateBits (n.eval kappa) (w.eval kappa) y) := by
  rw [phfeClass_eval, quadClass_eval, phfeEval_eq]
  apply congrArg₂ (quadEval _ _) <;> funext i <;>
    simp only [decodeResidues_block, duplicatePrivateBits_eq,
      Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, id_eq]
