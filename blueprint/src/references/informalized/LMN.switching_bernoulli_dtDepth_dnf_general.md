<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: switching_bernoulli_dtDepth_dnf_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Switching lemma for arbitrary DNFs

**Claim.** Let `f : DNF n` with `f.width ≤ w`, `0 < w`, `0 < n`, and let
`p : ℝ` satisfy `0 < p`, `p ≤ 1 / (40 * w)`, `p ≤ 1`. Then for every `t : ℕ`,
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f.eval ρ) > t) ≤
(1/2 : ℝ) ^ t + Real.exp (-(n * p / 3))`. This is
`switching_bernoulli_dtDepth_dnf` with the two syntactic hypotheses removed: `f`
need not have duplicate-free terms nor variable-injective terms.

**Proof.** Normalise `f` and apply the restricted version.

1. `h_eq : ∀ x, (cleanDNF f).eval x = f.eval x` is `cleanDNF_eval f`.
2. `rw [show f.eval = (cleanDNF f).eval from funext (fun x => (h_eq x).symm)]`
   replaces `f.eval` by `(cleanDNF f).eval` inside the probability — the event is
   a function of `f.eval` only, so this is a rewrite of equal terms.
3. `exact switching_bernoulli_dtDepth_dnf (cleanDNF f) w …` with the four
   hypotheses now available for the cleaned formula:
   `le_trans (cleanDNF_width_le f) hw` for the width, `cleanDNF_var_inj f` and
   `cleanDNF_nodup f` for the syntactic conditions, and `hn, hp_pos, hp_le, hp1, t`
   passed through unchanged. ∎

**Used in.** `depth2_circuit_switching_bound` and `lit_dnf` /
`depth2OrToDNF` cases in `CircuitLayerReduction.lean`, plus
`RecursiveReduction.lean` and `CompressionStep.lean` — everywhere a DNF
extracted from a circuit has no reason to be already normalised.
