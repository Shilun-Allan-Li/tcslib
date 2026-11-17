<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean :: SwitchingBernoulli.switching_bernoulli_dtDepth_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching bound for CNFs

**Claim.** For a CNF of width at most $w$ satisfying the stated distinct-variable and no-duplicate-literal conditions, the Bernoulli restriction probability that the restricted function has decision-tree depth greater than $t$ is at most $2^{-t}+\exp(-np/3)$.

**Proof.** Apply the DNF switching bound to the dual DNF of the given CNF. The dual has the same width, and the hypotheses on distinct variables and duplicate literals transfer to its terms. This gives the claimed probability bound for the restricted dual. By the evaluation identity for the dual, the restricted CNF computes the Boolean complement of the restricted dual. Complementing a Boolean function does not change its decision-tree depth, so the two events have the same probability, yielding the result.

**Key facts.** `CNF.dual_width`, `CNF.dual_inj`, `CNF.dual_nodup`, `SwitchingBernoulli.switching_bernoulli_dtDepth_dnf`, `CNF.dual_eval`, `dtDepth_neg`.
