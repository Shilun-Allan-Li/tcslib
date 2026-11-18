/-- Applying the input matrix to forward values cancels every internal prefix
row and leaves exactly the polynomial vector on output rows.

**Proof sketch.** Use the variable/constant edge readers and the Fin.snoc product
recurrence. At each non-root prefix its parent's weighted forward value cancels
its own value. Output rows sum the coefficient-weighted full prefix products. -/
theorem forward_action (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) :
    Matrix.mulVec (matrix C x) (forward x) =
      Sum.elim (fun _ : TIdx l d => 0) (polyTensorEval C x) := by
  funext row
  cases row with
  | inl v =>
    -- The abstract incidence action is the parent-to-child cancellation.
    change Matrix.mulVec (matrix C x) (forward x) (Sum.inl v) = 0
    have h := congrFun
      (PathAlgebra.weightedIncidence_mulVec
        (parent : TIdx l d → MIdx l d) node
        (fun w => xhat x (lastLabel w)) (forward x)) v
    simpa only [Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply,
      Matrix.transpose_apply, Matrix.of_apply, op_smul_eq_mul, matrix_inl,
      forward_node, mul_comm, sub_self] using h
  | inr j =>
    -- The zero variable block leaves the terminal coefficient rows.
    change Matrix.mulVec (matrix C x) (forward x) (Sum.inr j) = polyTensorEval C x j
    simp only [Matrix.mulVec_eq_sum, Finset.sum_apply, Pi.smul_apply,
      Matrix.transpose_apply, op_smul_eq_mul, matrix_eq, Matrix.add_apply,
      Matrix.mul_apply, L1_inr, zero_mul, Finset.sum_const_zero, zero_add, L0_inr]
    -- Swap the node and tuple sums; each tuple selects precisely its own leaf.
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [ite_mul, zero_mul, Fintype.sum_ite_eq', leaf_eq, forward_eq,
      Fin.val_last, polyTensorEval_eq]
