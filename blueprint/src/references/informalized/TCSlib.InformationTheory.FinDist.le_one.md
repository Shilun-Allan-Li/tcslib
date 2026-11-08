<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Outcome Has Probability at Most One

**Claim.** For a probability distribution $p$ on a finite set $\alpha$, every outcome $a\in\alpha$ has probability at most one.

**Proof.** The total probability is $1$. It is the sum of the probability at $a$ and the probabilities at all other outcomes. Every summand is nonnegative, so the full sum is at least $p(a)$; therefore $p(a)\le 1$.
