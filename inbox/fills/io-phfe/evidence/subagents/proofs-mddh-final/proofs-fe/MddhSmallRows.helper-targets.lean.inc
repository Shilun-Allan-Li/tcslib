-- SEARCH-ONLY PROPOSALS. No new helper proof is supplied.
-- Proposed independent home: MatrixDH/FiniteLinear.lean, namespace Pairing.

/-- A surjective scalar column map sends a uniform coefficient matrix to a uniform output
matrix. This is finite-field distribution glue; no sampler or machine is constructed.

**Proof sketch.** Regard the matrix product as independent applications of the surjective
linear map to each column. All fibers are translates of its kernel and have equal size;
reuse the finite linear quotient/fiber and uniform-average APIs. -/
theorem expect_sample_matrix_mul_of_mulVec_surjective
    {K : Type} [Field K] [Fintype K] {r m c : ℕ}
    (M : Matrix (Fin r) (Fin m) K) (hM : Function.Surjective (Matrix.mulVec M))
    (F : Matrix (Fin r) (Fin c) K → ℝ) :
    ProbComp.expect (ProbComp.sample (Matrix (Fin m) (Fin c) K)) (fun S => F (M * S)) =
      ProbComp.expect (ProbComp.sample (Matrix (Fin r) (Fin c) K)) F := sorry

/-- A uniform matrix with two columns and at most two rows fails surjectivity with
probability at most `2/|K|`. This is the exact rank-failure obligation for small-row MDDH.

**Proof sketch.** Split the row count into zero, one and two. Zero rows are automatically
surjective. One row fails only at the zero row, with mass `|K|⁻²`. For two rows use the
existing finite-field general-linear cardinality formula to obtain singular mass
`|K|⁻¹+|K|⁻²-|K|⁻³ ≤ 2/|K|`. -/
theorem smallRows_surjectivity_failure_le {K : Type} [Field K] [Fintype K]
    (r : ℕ) (hr : r ≤ 2) :
    ProbComp.prob (ProbComp.sample (Matrix (Fin r) (Fin 2) K))
        (fun M => ¬ Function.Surjective (Matrix.mulVec M)) ≤
      2 / (Fintype.card K : ℝ) := sorry
