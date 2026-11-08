<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.seqSelf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of Bounded Sequential Execution

**Claim.** If $s_1;s_2$ executes within $T$ from $\sigma$ to a state satisfying $Q$, then $s_1;s_2$ executes within $T$ from $\sigma$ to a state satisfying $Q$.

**Proof.** The given bounded execution is already the execution asserted by the conclusion, with the same cost bound and final-state condition.
