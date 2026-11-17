<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.notHaltedProb_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on Nonhalting Probability

**Claim.** For every natural number $t$, the probability that a procedure has not halted on a uniformly random length-$t$ string is at most $1$.

**Proof.** The nonhalting probability is an instance of the probability of an event under the uniform distribution on length-$t$ strings. Every such event has probability at most one (`Randomized.randProb_le_one`), which gives the claim.

**Key facts.** `Randomized.randProb_le_one`.
