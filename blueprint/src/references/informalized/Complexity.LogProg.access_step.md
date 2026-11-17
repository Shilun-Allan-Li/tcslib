<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One access-machine transition

**Claim.** If a configuration is in access state $st$ and all work-tape head positions lie in the stated safe interval, then one access-machine transition gives a finite safe computation path to the resulting configuration.

**Proof.** The path consisting of one transition is safe because its starting configuration satisfies the assumed safety condition. The transition is an ordinary machine step: the access program has no oracle-call state, so its recursive step agrees with the underlying Turing-machine step (`rstep_noncall`). With the state fixed to $st$, that machine step is exactly the action prescribed by the access transition function. Hence the one-step path ends at the claimed configuration.

**Key facts.** `Complexity.LogProg.rstep_noncall`.
