/-- If either canonical diagonal entry is nonzero, the transpose of the three-by-two
canonical DLIN base maps three scalar coordinates onto two. This is fixed scalar-matrix
geometry for the direct column route to [Wee20, §2.1, p. 4].

**Proof sketch.** Apply the published right-inverse characterization of a surjective matrix
column map. A nonzero first or second diagonal entry supplies the corresponding right
inverse using division by that known nonzero scalar; matrix entry readers verify it. -/
theorem dlin_base_transpose_mulVec_surjective {K : Type} [Field K]
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Surjective
      (Matrix.mulVec ((![![a, 0], ![0, b], ![1, 1]] :
        Matrix (Fin 3) (Fin 2) K)ᵀ)) := by
  apply (Matrix.mulVec_surjective_iff_exists_right_inverse
    (A := ((![![a, 0], ![0, b], ![1, 1]] : Matrix (Fin 3) (Fin 2) K)ᵀ))).2
  rcases hab with ha | hb
  · -- Use the first nonzero diagonal entry to construct a scalar right inverse.
    refine ⟨(![![a⁻¹, -a⁻¹], ![0, 0], ![0, 1]] :
      Matrix (Fin 3) (Fin 2) K), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply, mul_zero, zero_mul,
        one_mul, mul_one, mul_neg, mul_inv_cancel₀ ha, add_zero, zero_add,
        neg_add_cancel] <;> norm_num <;>
        simp only [mul_inv_cancel₀ ha, neg_add_cancel]
  · -- The second nonzero diagonal entry gives the symmetric scalar right inverse.
    refine ⟨(![![0, 0], ![-b⁻¹, b⁻¹], ![1, 0]] :
      Matrix (Fin 3) (Fin 2) K), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply, mul_zero, zero_mul,
        one_mul, mul_one, mul_neg, mul_inv_cancel₀ hb, add_zero, zero_add,
        neg_add_cancel] <;> norm_num <;>
        simp only [mul_inv_cancel₀ hb, neg_add_cancel]
