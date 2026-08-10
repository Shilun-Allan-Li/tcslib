<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: switching_bernoulli_dtDepth_cnf_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Switching lemma for arbitrary CNFs

**Claim.** Let `f : CNF n` with `CNF.width f ≤ w`, `0 < w`, `0 < n`, and let
`p : ℝ` satisfy `0 < p`, `p ≤ 1 / (40 * w)`, `p ≤ 1`. Then for every `t : ℕ`,
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn (CNF.eval f) ρ) > t) ≤
(1/2 : ℝ) ^ t + Real.exp (-(n * p / 3))`. This is
`switching_bernoulli_dtDepth_cnf` with its two syntactic hypotheses (clauses
duplicate-free, clauses variable-injective) dropped.

**Proof.** Mirror of the DNF case: normalise, then apply the restricted version.

1. `h_eq : ∀ x, CNF.eval (cleanCNF f) x = CNF.eval f x` is `cleanCNF_eval f`.
2. `rw [show CNF.eval f = CNF.eval (cleanCNF f) from funext (fun x => (h_eq x).symm)]`
   swaps in the cleaned formula inside the probability.
3. `exact switching_bernoulli_dtDepth_cnf (cleanCNF f) w …`, discharging its
   hypotheses with `le_trans (cleanCNF_width_le f) hw`, `cleanCNF_var_inj f`,
   `cleanCNF_nodup f`, and the untouched `hn, hp_pos, hp_le, hp1, t`. ∎

**Used in.** `RecursiveReduction.lean` and the `depth2AndToCNF` branch of
`depth2_circuit_switching_bound` (`CircuitLayerReduction.lean`), where a CNF read
off a depth-2 AND-gate carries no normalisation guarantees.
