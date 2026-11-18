/-- The probability that a uniform square matrix over a finite field is a unit is the
published general-linear-group cardinality divided by the cardinality of all matrices.
The numerator uses natural subtraction, and the formula includes dimension zero.

**Proof sketch.** Read prob_sample_eq_uprob and uprob_def. Identify the unit predicate
subtype with the range of Units.val and use card_range_of_injective val_injective.
Apply Matrix.card_GL_field and the existing function-cardinality/power laws. -/
theorem prob_sample_matrix_isUnit_eq {K : Type} [Field K] [Fintype K] (n : ℕ) :
    ProbComp.prob (ProbComp.sample (Matrix (Fin n) (Fin n) K)) (fun M => IsUnit M) =
      (((∏ i : Fin n,
          (Fintype.card K ^ n - Fintype.card K ^ (i : ℕ))) : ℕ) : ℝ) /
        (Fintype.card K : ℝ) ^ (n * n) := sorry
