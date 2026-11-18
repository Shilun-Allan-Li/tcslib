/-- The two random presentations differ by at most the probability of a zero diagonal
coordinate [GJLS21, Definition 3.3, p. 18; JLS26, §1.1, p. 3]. This correction is explicit;
the source presentations are not asserted to have identical random laws.

**Proof sketch.** Condition on the diagonal scalars. Off the zero-coordinate event,
multiplication by each nonzero scalar bijects its uniform mask with a uniform response.
Use `expect_sample_equiv` for those bijections. Bound the acceptance difference by one on
the exceptional event, whose exact probability is `2/p - 1/p^2`, and average over group coins. -/
theorem dlinMatrixGame_random_gap_le (D : NUPPT) (κ : ℕ) :
    |accept (G.dlinMatrixGame D false κ) - accept (G.dlinGame D false κ)| ≤
      G.dlinMatrixSlack κ := sorry
