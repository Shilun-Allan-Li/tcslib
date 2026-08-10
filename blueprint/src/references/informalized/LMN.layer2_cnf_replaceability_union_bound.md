<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: layer2_cnf_replaceability_union_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Union bound for layer-2 CNF-replaceability

**Claim.** Let `gates : Fin s₂ → DNF n` be the layer-2 gates, each of width
`≤ w` with `0 < w`, each term variable-distinct (`hnd`) and `Nodup`, `0 < n`, and
`0 < p ≤ 1/(40w)` with `p ≤ 1`. Then the Bernoulli(`p`) probability that *some*
gate `i` fails to have a CNF `ψ` with `ψ.width ≤ l` computing
`restrictFn (gates i).eval ρ` is at most `s₂ · ((1/2)^l + exp(-n·p/3))`.

**Proof.** The stated event is weakened into the depth event already bounded
gatewise.

1. `refine' le_trans _ (switching_bernoulli_union_bound gates w l …)`, so it
   remains to bound the CNF-failure probability by
   `bernoulliRestrProb p (fun ρ => ∃ i, dtDepth (restrictFn (gates i).eval ρ) > l)`;
   `all_goals norm_cast at *` discharges the side hypotheses.
2. `convert bernoulliRestrProb_mono p hp_pos.le hp1 _ _ _ using 3` reduces that
   to a pointwise implication between the two events.
3. The implication: given `⟨i, hi⟩` with `hi` saying no width-`l` CNF exists for
   gate `i`, produce `⟨i, not_le.mp …⟩`; the inner map sends a hypothetical
   `dtDepth ≤ l` to a CNF via `restricted_has_small_cnf_of_dtDepth_le`,
   contradicting `hi`, hence `dtDepth > l`. ∎

**Used in.** `layer2_cnf_replaceability_simplified`, which absorbs the
`exp(-n·p/3)` tail into an additive `ε`.
