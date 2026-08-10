<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: depth3_second_stage_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Second-stage switching bound for a successfully switched depth-3 circuit

**Claim.** Let `f : (Fin n → Bool) → Bool` be the AND of `s₂` DNF gates
(`h_f : ∀ x, f x = true ↔ ∀ i, (gates i).eval x = true`), let `ρ₁` be a
restriction under which every gate has already switched, i.e.
`dtDepth (restrictFn (gates i).eval ρ₁) ≤ l` for all `i`, and assume `0 < l`,
`0 < n`, `0 < p₂ ≤ 1/(40 l)` and `p₂ ≤ 1`. Then under a fresh Bernoulli(`p₂`)
restriction `ρ₂`,

`bernoulliRestrProb p₂ (fun ρ₂ => dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t) ≤ (1/2)^t + exp(−n·p₂/3)`.

**Proof.** Reduce to the CNF switching lemma
`switching_bernoulli_dtDepth_cnf` applied to a cleaned width-`l` CNF for
`restrictFn f ρ₁` (`convert switching_bernoulli_dtDepth_cnf _ … using 1`).

1. Take `Ψ := cleanCNF_D3 (Classical.choose (depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates))`
   — stage 1 supplies a width-`l` CNF equal to `restrictFn f ρ₁` pointwise, and
   `cleanCNF_D3` normalizes it. Instantiate the switching-lemma width parameter
   at `l`.
2. Width hypothesis: `cleanCNF_D3_width_le` composed with the first component of
   `Classical.choose_spec` gives `CNF.width Ψ ≤ l`.
3. Clause hypotheses: `cleanCNF_D3_var_inj` and `cleanCNF_D3_nodup` supply
   variable-injectivity and `Nodup` for every clause of `Ψ`.
4. Event hypothesis: `cleanCNF_D3_eval` plus `Classical.choose_spec` give
   `∀ x, CNF.eval Ψ x = restrictFn f ρ₁ x` (`h_eq`); then
   `restrictFn_composeRestr` splits the composed restriction into `ρ₁` followed by
   `ρ₂`, and `dtDepth_congr _ _ (… restrictFn_congr _ _ _ h_eq)` identifies
   `dtDepth (restrictFn f (composeRestr ρ₁ ρ₂))` with
   `dtDepth (restrictFn (CNF.eval Ψ) ρ₂)`, matching the two events. The numeric
   side goals (`0 < l`, `0 < n`, the `p₂` bounds) go through by
   `any_goals assumption`.

**Used in.** `depth3_switching_bound`, as the conditional stage-2 bound fed to
`two_stage_bound` for every `ρ₁` outside the stage-1 failure event.

**Caveat.** The chain runs through `cleanCNF_D3_eval`, which depends on
`dedupClauseVars_eval_of_not_taut` — currently a `sorry` in this file — so this
bound is not yet fully proved.
