<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: switching_bernoulli_gate_to_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A DNF gate becomes a narrow CNF after a Bernoulli restriction

**Claim.** Let `g : DNF n` have width `≤ w` with `0 < w`, no two literals in a
term sharing a variable (`hnd`) and every term `Nodup`, let `0 < n`, and let
`0 < p ≤ 1/(40w)` with `p ≤ 1`. Then under a Bernoulli(`p`) random restriction
the probability that `g|_ρ` admits *no* CNF `ψ` of width `≤ l` computing it
pointwise is at most `(1/2)^l + exp(-n·p/3)`.

**Proof.** The failure event is weakened into the decision-tree event already
bounded by the switching lemma.

1. `apply le_trans _ (switching_bernoulli_dtDepth_dnf g w … l)` reduces the goal
   to comparing the CNF-failure probability with
   `bernoulliRestrProb p (fun ρ => dtDepth (restrictFn g.eval ρ) > l)`, whose
   bound `(1/2)^l + exp(-n·p/3)` is exactly the Bernoulli switching lemma.
2. `apply bernoulliRestrProb_mono p hp_pos.le hp1` reduces that comparison to a
   pointwise implication: for each `ρ`, "no width-`l` CNF for `g|_ρ`" implies
   `dtDepth (restrictFn g.eval ρ) > l`.
3. Prove the implication contrapositively: `by_contra` and `push_neg` give
   `dtDepth (restrictFn g.eval ρ) ≤ l`, whence
   `(dtDepth_le_implies_small_dnf_cnf _ l h_not_gt).2` produces a width-`≤ l`
   CNF, contradicting the hypothesis. ∎

**Used in.** The bridge from "small decision-tree depth" to "narrow CNF" used by
the layer-2 replaceability bounds; the CNF-side dual is
`switching_bernoulli_gate_to_dnf_from_cnf`.
