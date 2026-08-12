<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxAndPolyList_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The AND-approximator list has `2^(width·ℓ)` entries

**Claim.** `(approxAndPolyList p polys).length = 2 ^ (width * ℓ)`.

**Proof.** Two steps, after `classical` supplies the decidability needed for the
`Finset`.

1. `simp [approxAndPolyList]` sees through `Finset.univ.toList.map`: mapping
   preserves length and `toList` has the length of the `Finset`, so the goal
   becomes `Fintype.card (Fin ℓ → Finset (Fin width)) = 2 ^ (width * ℓ)`.
2. `approxSeed_card width ℓ` is exactly that count — a function from `Fin ℓ` into
   the `2^width` subsets of `Fin width` gives `(2^width)^ℓ = 2^(width*ℓ)`.

**Remark.** The seed count is the denominator of the probabilistic argument: paired
with the bad-seed bound `(bad seeds) * 2^ℓ ≤ 2^(width*ℓ)`
(`approxAnd_pointwise_bad_count`), it says the failure probability for a fixed
input is at most `2^(-ℓ)`.

**Used in.** `exists_good_approxAnd` only (same file), where it supplies both the
list's stated length and — read backwards — the right-hand side of the bad-count
inequality. No external consumers; `CircuitDegree.lean` calls `approxSeed_card`
directly instead.
