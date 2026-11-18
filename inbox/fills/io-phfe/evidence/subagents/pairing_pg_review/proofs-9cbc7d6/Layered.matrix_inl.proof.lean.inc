/-- A non-root input-matrix row has its padded edge weight at the parent and a
negative unit at its node. This is the layered incidence formula of
[AGW20, Appendix A, (32), p.38].

**Proof sketch.** Evaluate the abstract padded-incidence identity at the chosen
row and column. Identify its matrices using the published incidence, public-input
and padding readers, with the product-index sum formula. -/
theorem matrix_inl (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (v : TIdx l d) (u : MIdx l d) :
    matrix C x (Sum.inl v) u =
      (if u = parent v then xhat x (lastLabel v) else 0) -
        (if u = node v then 1 else 0) := by
  have h := congrArg
    (fun B : Matrix (TIdx l d) (MIdx l d) (ZMod (p : ℕ)) => B v u)
    (PathAlgebra.paddedIncidence_eq
      (parent : TIdx l d → MIdx l d) node lastLabel x)
  simpa only [matrix_eq, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, L1_inl, L0_inl, PartialGarbling.publicTensor_apply,
    xhat_eq] using h
