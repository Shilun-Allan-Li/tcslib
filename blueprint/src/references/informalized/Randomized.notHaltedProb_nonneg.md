<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.notHaltedProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Nonhalting Probability

**Claim.** For every natural number $t$, the probability that a procedure has not halted on a uniformly random length-$t$ string is nonnegative.

**Proof.** The nonhalting probability is the probability of an event under the uniform distribution on length-$t$ strings. Such a probability is nonnegative (`Randomized.randProb_nonneg`).

**Key facts.** `Randomized.randProb_nonneg`.
