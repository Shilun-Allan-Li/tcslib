<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: balanced_totalInfluence_ge_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A balanced ±1 function has total influence at least one

**Claim.** If `f : BooleanFunc n` is `±1`-valued (`isPmOne f`) and balanced
(`expect f = 0`), then `totalInfluence f ≥ 1`.

**Proof.** Compare the two Parseval-style sums term by term: the total influence
weights each frequency by `|S|`, while Parseval weights it by `1`, and balance
removes the only frequency where that comparison could fail.

1. `rw [ge_iff_le, ← parseval_pm_one f hf, totalInfluence_eq_sum_sq_deg]` turns
   the goal into `∑_S f̂(S)² ≤ ∑_S |S| · f̂(S)²`, using `∑_S f̂(S)² = 1`
   for `±1`-valued `f` and `I[f] = ∑_S |S| · f̂(S)²`.
2. `apply Finset.sum_le_sum` reduces to one frequency `S` at a time.
3. Case `S = ∅`: `simp [hS, fourierCoeff_empty, hbal]` — the coefficient is
   `f̂(∅) = expect f = 0`, so both sides vanish and the missing factor `|∅| = 0`
   does no harm. This is the only place balance is used.
4. Case `S ≠ ∅`: `1 ≤ S.card` by
   `Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)`, so
   `f̂(S)² = 1 * f̂(S)² ≤ |S| · f̂(S)²` by
   `mul_le_mul_of_nonneg_right _ (sq_nonneg _)`. ∎

**Remark.** The hypothesis `_hn : 0 < n` is underscore-prefixed and genuinely
unused — the argument needs no positivity, since for `n = 0` the balance
hypothesis is already contradictory (`f` is `±1`-valued on a one-point cube, so
`expect f = f x = ±1 ≠ 0`).

**Used in.** Nothing — no other declaration in the repository references it.
Its proof is nonetheless live: `KKL_balanced` re-derives the identical statement
inline as its own `have hI : 1 ≤ totalInfluence f` (lines 585–596) with the same
four steps, rather than calling this lemma. So this is a duplicated, extracted
copy of a step inside a theorem that still carries a `sorry` — a natural
candidate for the consumer to be rewired to.
