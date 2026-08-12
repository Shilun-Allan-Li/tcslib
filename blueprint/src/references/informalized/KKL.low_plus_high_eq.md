<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: low_plus_high_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Low-degree plus high-degree part recovers the function

**Claim.** Pointwise, for every `x : BoolCube n`,
`lowDegreePart f k x + highDegreePart f k x = f x`.

**Proof.**

- Unfold both definitions and merge the two sums with `Finset.sum_add_distrib`,
  so the goal is one sum over `S` of paired guarded terms.
- The termwise identity
  `(if S.card ≤ k then f̂(S)·χ_S(x) else 0) + (if k < S.card then f̂(S)·χ_S(x) else 0)
   = f̂(S)·χ_S(x)`
  is proved by `by_cases h : S.card ≤ k`, using `Nat.not_lt.mpr h` in one branch
  and `Nat.lt_of_not_le h` in the other to discharge the complementary guard —
  exactly one of the two guards fires.
- Rewriting with `Finset.sum_congr rfl this` leaves `∑ S, f̂(S)·χ_S(x) = f x`,
  which is `(walsh_expansion f x).symm`. ∎

**Used in.** `lowDegree_l2_error`, where the `hfg` step turns it into
`f x - lowDegreePart f k x = highDegreePart f k x` by `linarith`. That
subtraction form, not the sum form, is what the rest of the file uses.
