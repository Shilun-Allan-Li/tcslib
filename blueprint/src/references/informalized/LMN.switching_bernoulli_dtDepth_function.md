<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: switching_bernoulli_dtDepth_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Switching lemma stated for functions, not formulas

**Claim.** Let `f : (Fin n → Bool) → Bool` with `dtDepth f ≤ w`, `0 < w`,
`0 < n`, and `0 < p ≤ 1/(40w)` with `p ≤ 1`. Then for every `t`,
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ (1/2)^t + exp(-n·p/3)`.

**Proof.** Replace `f` by a formula and quote the CNF switching lemma.

1. `dtDepth_le_implies_nice_cnf f w h` gives `ψ : CNF n` with
   `CNF.width ψ ≤ w`, `CNF.eval ψ = f` pointwise, and the `Nodup` /
   variable-injective clause conditions.
2. `h_eq`: for every `ρ`,
   `dtDepth (restrictFn f ρ) = dtDepth (restrictFn (CNF.eval ψ) ρ)`, by
   `dtDepth_congr` applied to `restrictFn_congr` — restriction of pointwise-equal
   functions stays pointwise equal, and `dtDepth` only sees the function.
3. `calc`: rewrite the event with `congr 1; ext ρ; rw [h_eq]`, then close with
   `switching_bernoulli_dtDepth_cnf ψ w hw_ψ hw_pos hvarinj_ψ hnodup_ψ hn p hp_pos hp_le hp1 t`. ∎

**Why it matters.** The second stage of the depth-3 argument has only a
*function* (the restricted circuit `f|_ρ₁`) in hand, not a syntactic formula, so
the formula-level switching lemma cannot be applied directly; this is the
function-level restatement. It inherits the `sorry` in
`dedupClauseVars_eval_of_not_taut` via `dtDepth_le_implies_nice_cnf`, and is
currently not referenced elsewhere (`depth3_second_stage_bound` inlines the same
argument with `Classical.choose`).
