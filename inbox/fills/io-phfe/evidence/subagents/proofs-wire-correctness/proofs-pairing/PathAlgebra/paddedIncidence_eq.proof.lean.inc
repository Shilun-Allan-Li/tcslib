/-- A variable incidence matrix contracted against the public-input tensor,
plus its constant-edge and negative-child entries, equals the weighted endpoint
matrix with the constant 1 appended to the input. This abstracts the split in
[AGW20, Appendix A, (32), p.38] to an arbitrary ring and arbitrary endpoint maps. 

**Proof sketch.** Contract the product-indexed matrix using the published finite-sum
readers. Split the edge label into a variable coordinate or the final constant coordinate;
the corresponding one-coordinate sum yields the padded input value. -/
theorem paddedIncidence_eq {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] {l : ℕ} (parent child : E → V) (label : E → Fin (l + 1))
    (x : Fin l → R) :
    (Matrix.of (fun e (iu : Fin l × V) =>
        if iu.2 = parent e ∧ label e = iu.1.castSucc then (1 : R) else 0) :
          Matrix E (Fin l × V) R) *
      (Matrix.of (fun (iu : Fin l × V) v =>
        x iu.1 * (if iu.2 = v then 1 else 0)) : Matrix (Fin l × V) V R) +
      Matrix.of (fun e v =>
        (if v = parent e ∧ label e = Fin.last l then 1 else 0) -
          (if v = child e then 1 else 0)) =
      Matrix.of (fun e v =>
        (if v = parent e then Fin.snoc (α := fun _ => R) x (1 : R) (label e) else 0) -
          (if v = child e then 1 else 0)) := by
  funext e v
  -- Contract the product index and its single supported node coordinate.
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_and, ite_mul, one_mul, zero_mul,
    Fintype.sum_ite_eq']
  have hlast (i : Fin l) : Fin.last l ≠ i.castSucc :=
    Ne.symm (Fin.castSucc_ne_last i)
  -- At the parent column, split the label into variable and constant cases.
  by_cases hv : v = parent e
  · subst v
    generalize label e = a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [hlast, if_false, if_true, Fin.snoc_last,
        Finset.sum_const_zero, zero_add]
    · simp only [Fin.castSucc_inj, Fin.castSucc_ne_last, if_false,
        Fin.snoc_castSucc, Fintype.sum_ite_eq, if_true, mul_one,
        sub_eq_add_neg, zero_add]
  -- Every other column has zero parent contribution on both sides.
  · simp only [if_neg hv, if_neg (Ne.symm hv), mul_zero, ite_self,
      Finset.sum_const_zero, zero_add]
