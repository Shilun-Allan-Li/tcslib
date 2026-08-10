<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: switching_bernoulli_gate_to_dnf_from_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A CNF gate becomes a narrow DNF after a Bernoulli restriction

**Claim.** The dual of `switching_bernoulli_gate_to_cnf`. Let `g : CNF n` have
width `≤ w` with `0 < w`, no repeated variable inside a clause (`hnd`), every
clause `Nodup`, `0 < n`, and `0 < p ≤ 1/(40w)` with `p ≤ 1`. Then under a
Bernoulli(`p`) restriction the probability that `g|_ρ` admits *no* DNF `φ` of
width `≤ l` computing it pointwise is at most `(1/2)^l + exp(-n·p/3)`.

**Proof.** Same three moves as the DNF case, against the CNF form of the
switching lemma.

1. `apply le_trans _ (switching_bernoulli_dtDepth_cnf g w … l)`, whose conclusion
   bounds `bernoulliRestrProb p (fun ρ => dtDepth (restrictFn (CNF.eval g) ρ) > l)`
   by `(1/2)^l + exp(-n·p/3)`.
2. `apply bernoulliRestrProb_mono p hp_pos.le hp1` leaves the pointwise
   implication "no width-`l` DNF for `g|_ρ`" → `dtDepth (restrictFn (CNF.eval g) ρ) > l`.
3. `by_contra` + `push_neg` gives `dtDepth ≤ l`, and the *first* component
   `(dtDepth_le_implies_small_dnf_cnf _ l h_not_gt).1` supplies the width-`≤ l`
   DNF that the hypothesis forbids. ∎

**Used in.** Provides the CNF→DNF direction needed when the iterative circuit
reduction alternates gate types between layers.
