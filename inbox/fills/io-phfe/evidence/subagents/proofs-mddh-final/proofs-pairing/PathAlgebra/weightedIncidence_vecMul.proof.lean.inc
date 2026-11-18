/-- The backward action of weighted endpoint rows is the sum of outgoing
weighted edge values minus the sum of incoming edge values at each node.
Repeated endpoints and loops are permitted; node finiteness is unnecessary. 

**Proof sketch.** Distribute the backward matrix action across subtraction. Read each
coordinate through the published vector-matrix action formula and conditional multiplication. -/
theorem weightedIncidence_vecMul {V E R : Type*} [Fintype E] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight flow : E → R) :
    Matrix.vecMul flow
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) =
      fun v =>
        (∑ e, if parent e = v then flow e * weight e else 0) -
          ∑ e, if child e = v then flow e else 0 := by
  change Matrix.vecMul flow
    ((Matrix.of fun e v => if v = parent e then weight e else 0) -
      (Matrix.of fun e v => if v = child e then (1 : R) else 0)) = _
  rw [Matrix.vecMul_sub]
  funext v
  simp only [Pi.sub_apply, Matrix.vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    Matrix.of_apply, smul_eq_mul, mul_ite, mul_zero, mul_one, eq_comm]
