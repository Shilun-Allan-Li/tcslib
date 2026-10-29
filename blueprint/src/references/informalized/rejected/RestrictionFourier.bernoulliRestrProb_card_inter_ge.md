<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: bernoulliRestrProb_card_inter_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At least `k` free coordinates in `U` with probability at least `1/4`

**Claim.** Let `0 ≤ p ≤ 1`, `U : Finset (Fin n)` and `k : ℕ` with `1 ≤ k` and
`3 * (k : ℝ) ≤ p * U.card`. Then
`1 / 4 ≤ bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card)`.

**Proof.**

1. Complement the event (`hcompl`): by `bernoulliRestrProb_not p hp0 hp1`
   applied to `fun ρ => (U ∩ ρ.freeVars).card < k`, and termwise
   `if_congr not_lt.symm` to identify `¬(· < k)` with `k ≤ ·`, the probability
   equals `1 - Pr[|U ∩ J| < k]`.
2. `bernoulliRestrProb_card_inter_lt p hp0 hp1 U k hk h3k` bounds that tail by
   `3 / (4 * k)`.
3. Since `1 ≤ (k : ℝ)` (`exact_mod_cast hk`), `3 / (4 * k) ≤ 3 / 4`
   (`div_le_div_iff₀`, `linarith`).
4. Hence the probability is at least `1 - 3/4 = 1/4` (`linarith`). ∎

**Used in.** `LMN/FourierConcentration.lean` (the restriction ⇒ Fourier
concentration transfer, O'Donnell Lemma 4.21), where the constant `1/4` — any
constant `> 0` — only rescales the final concentration bound.
