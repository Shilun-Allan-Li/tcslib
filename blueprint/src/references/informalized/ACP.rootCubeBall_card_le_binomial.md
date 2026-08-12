<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: rootCubeBall_card_le_binomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binomial bound for a Hamming ball on the root cube

**Claim.** Let `K` be a finite field, `ω : K`, and `center : rootCube ω n → K`. Then
`(rootCubeBall center e).card ≤ ∑ t ∈ Finset.range (e + 1), (Nat.card (rootCube ω n)).choose t * (Nat.card K) ^ t`:
the number of functions on the root cube differing from `center` in at most `e` places obeys
the standard binomial bound, with the coarse factor `|K|^t` in place of `(|K| - 1)^t`.

**Proof.** Immediate specialization of the general result.
- `letI` installs the intended instances: `Fintype.ofFinite K`, `rootCubeFintypeOfFintype`
  for the cube, and `Pi.instFintype` for the function space.
- Apply `function_hammingBall_card_le_binomial` with `α := rootCube ω n`, `β := K`, the same
  `center` and radius `e`.
- `simpa [rootCubeBall, rootCubeFunctionBadCount, Nat.card_eq_fintype_card]` unfolds the ball
  and its disagreement count into the filtered-`univ` form of the general lemma and converts
  between `Nat.card` and `Fintype.card`.

**Remark.** The coarser `|K|^t` factor is deliberate (see the docstring): it still suffices
for the counting line and is easier to reuse.
