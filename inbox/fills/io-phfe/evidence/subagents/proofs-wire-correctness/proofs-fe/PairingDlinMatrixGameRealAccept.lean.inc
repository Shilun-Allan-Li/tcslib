/-- The real tuple and compressed matrix presentations have identical acceptance laws
[GJLS21, Definition 3.3, p. 18; JLS26, §1.1, p. 3].

**Proof sketch.** Use `dlinMatrix_mulVec` to identify the response coordinates. Integrate
out the unused random response draws with the shared probability readers. The public group,
generator, diagonal scalars, coefficient vector and distinguisher coins coincide. -/
theorem dlinMatrixGame_real_accept (D : NUPPT) (κ : ℕ) :
    accept (G.dlinMatrixGame D true κ) = accept (G.dlinGame D true κ) := by
  simp only [accept_eq, dlinMatrixGame_eq, dlinGame_eq, dlinMatrixSample_eq,
    dlinSample_eq, ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
    ProbComp.prob_pure, ↓reduceIte, ProbComp.expect_const]
