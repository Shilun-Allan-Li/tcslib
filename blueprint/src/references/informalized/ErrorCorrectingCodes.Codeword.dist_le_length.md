<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: dist_le_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Minimum distance is at most the block length

**Claim.** If `d` is the minimum distance of a code `C : Code n α`, in the sense
of the predicate `distance C d`, then `d ≤ n`. Nothing is assumed about `C`
beyond `distance C d` — in particular `C` is not required to be nonempty, since
`distance` already asserts the existence of a witnessing pair.

**Proof.**

1. Split `distance C d` with `rcases`; only the first conjunct is used. It
   supplies codewords `c₁, c₂ ∈ C` with `c₁ ≠ c₂` and
   `hamming_distance c₁ c₂ = d` (hypothesis `hdeq`).
2. Bound the raw Hamming distance by the number of coordinates with a two-step
   `calc`: `hammingDist c₁ c₂ ≤ Fintype.card (Fin n)` by
   `hammingDist_le_card_fintype`, and `Fintype.card (Fin n) = n` by
   `Fintype.card_fin n`.
3. Unfold `hamming_distance` in `hdeq` (`dsimp [hamming_distance]`) so that it
   becomes an equation about `hammingDist`, then `rw [hdeq]` turns the bound of
   step 2 into `d ≤ n`, which closes the goal.

The distinctness hypothesis `c₁ ≠ c₂` is never needed; the argument only uses
that *some* pair realises the distance.

**Used in.** `singleton_bound` (`SingletonBound.lean`, three places, including
the `Nat.sub_sub_self` step) and the volume bound in `HammingBound.lean`.
