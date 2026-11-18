-- HEADER ONLY. Native typing/exact?/apply? must precede any proof.
-- Suggested home: MatrixDH/ColumnLaws.lean before the bounded-test column law.

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
        Matrix (Fin 3) (Fin 2) K)ᵀ)) := sorry
