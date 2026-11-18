/-- Multiplying the backward draw shift by the input matrix cancels every column
except the source column, whose value is the allowed scalar.

**Proof sketch.** Split each nonempty suffix into first label and remaining
suffix using Fin.consEquiv, and use Fin.snoc to extend the prefix. Thus each
internal column's weighted child sum equals its backward value and cancels its
negative diagonal. Terminal columns use the coefficient-weighted z values.
The source has no negative diagonal; apply backward_root there. -/
theorem backward_action (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) :
    Matrix.vecMul (shift C x z) (matrix C x) =
      fun u => if u = root l d then dotProduct z (polyTensorEval C x) else 0 := by
  let edges : Matrix (TIdx l d) (MIdx l d) (ZMod (p : ℕ)) :=
    Matrix.of (fun v u =>
      (if u = parent v then xhat x (lastLabel v) else 0) -
        (if u = node v then 1 else 0))
  let outputs : Matrix (Fin n) (MIdx l d) (ZMod (p : ℕ)) :=
    Matrix.of (fun j u =>
      ∑ tau : Fin d → Fin (l + 1), if u = leaf tau then C j tau else 0)
  -- Read the source matrices as the two row blocks.
  have hMatrix : matrix C x = Matrix.fromRows edges outputs := ?_
  swap
  · funext row u
    cases row with
    | inl v =>
      rw [Matrix.fromRows_apply_inl]
      change matrix C x (Sum.inl v) u =
        (if u = parent v then xhat x (lastLabel v) else 0) -
          (if u = node v then 1 else 0)
      exact matrix_inl C x v u
    | inr j =>
      rw [Matrix.fromRows_apply_inr]
      change matrix C x (Sum.inr j) u =
        ∑ tau : Fin d → Fin (l + 1), if u = leaf tau then C j tau else 0
      simp only [matrix_eq, Matrix.add_apply, Matrix.mul_apply, L1_inr,
        zero_mul, Finset.sum_const_zero, zero_add, L0_inr]
  have hShift : shift C x z =
      Sum.elim (fun v => backward C x z (node v)) z :=
    (Sum.elim_comp_inl_inr (shift C x z)).symm.trans
      (congrArg₂ Sum.elim (funext (shift_inl C x z)) (funext (shift_inr C x z)))
  -- The output block contributes exactly the terminal coefficient sum.
  have hOutput : Matrix.vecMul z outputs = fun u =>
      ∑ tau : Fin d → Fin (l + 1),
        if u = leaf tau then (∑ j : Fin n, C j tau * z j) else 0 := ?_
  swap
  · funext u
    rw [congrFun (Matrix.vecMul_eq_sum z outputs) u]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ j : Fin n, z j *
      (∑ tau : Fin d → Fin (l + 1), if u = leaf tau then C j tau else 0)) =
        ∑ tau : Fin d → Fin (l + 1),
          if u = leaf tau then (∑ j : Fin n, C j tau * z j) else 0
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, mul_comm]
  have hEdges := PathAlgebra.weightedIncidence_vecMul
    (parent : TIdx l d → MIdx l d) node
    (fun v => xhat x (lastLabel v)) (fun v => backward C x z (node v))
  rw [hShift, hMatrix, Matrix.sumElim_vecMul_fromRows, hEdges, hOutput]
  funext u
  simp only [Pi.add_apply]
  -- Specialize generic suffix conservation through the published path readers.
  have hBalance :
      (∑ v : TIdx l d,
        if parent v = u then backward C x z (node v) * xhat x (lastLabel v) else 0) +
      (∑ tau : Fin d → Fin (l + 1),
        if u = leaf tau then (∑ j : Fin n, C j tau * z j) else 0) =
        backward C x z u := ?_
  swap
  · simpa only [parent_eq, node_eq, lastLabel_eq, leaf_eq, backward_eq, extend_eq] using
      (PrefixAlgebra.prefixFlow_balance d
        (fun tau => ∑ j : Fin n, C j tau * z j) (xhat x) u)
  have hIncoming :
      (∑ v : TIdx l d,
        if node v = u then backward C x z (node v) else 0) =
      if u = root l d then 0 else backward C x z u := ?_
  swap
  · simpa only [node_eq, root_eq] using
      (PrefixAlgebra.prefixIncoming_sum d (backward C x z) u)
  -- Incoming cancellation leaves only the unbalanced source value.
  rw [sub_add_eq_add_sub, hBalance, hIncoming]
  by_cases hu : u = root l d
  · subst u
    simp only [eq_self, if_true, sub_zero, backward_root]
  · simp only [hu, if_false, sub_self]
