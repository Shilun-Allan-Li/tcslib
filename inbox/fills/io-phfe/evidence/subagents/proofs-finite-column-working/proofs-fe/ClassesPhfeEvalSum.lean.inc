/-- PHFE evaluation has exactly the sum-of-quadratic-terms form required in §9.
[GJLS21, §9, pp.57–58].

**Proof sketch.** Reindex the flattened private tensor by finProdFinEquiv, then
commute scalar factors in each term. Reuse finite-product sum reindexing. -/
theorem phfeEval_sum {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l (n * n) d)
    (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)) :
    phfeEval C x y = ∑ j : Fin n, ∑ k : Fin n,
      polyTensorEval C x (finProdFinEquiv (j, k)) * y j * y k := by
  rw [phfeEval_eq, quadEval_eq]
  show (∑ i : Fin (n * n), privateTensor y y i * polyTensorEval C x i) = _
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply,
    mul_comm, mul_left_comm, mul_assoc]
