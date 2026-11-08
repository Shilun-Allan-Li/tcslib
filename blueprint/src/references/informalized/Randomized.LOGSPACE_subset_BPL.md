<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.LOGSPACE_subset_BPL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Is Contained in Bounded-Error Probabilistic Logspace

**Claim.** Every language decidable in deterministic logarithmic space is decidable in bounded-error probabilistic logarithmic space.

**Proof.** The deterministic logspace containment in randomized logspace gives $\mathrm{LOGSPACE}\subseteq\mathrm{RL}$ (\texttt{LOGSPACE\_subset\_RL}). Randomized logspace is contained in bounded-error probabilistic logspace, so $\mathrm{RL}\subseteq\mathrm{BPL}$ (\texttt{RL\_subset\_BPL}). By transitivity of set inclusion, $\mathrm{LOGSPACE}\subseteq\mathrm{BPL}$.

**Key facts.** `Randomized.LOGSPACE_subset_RL`, `Randomized.RL_subset_BPL`.
