<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Meets.of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Call from Its Body

**Claim.** If procedure $p$ has body $s$, and executing $s$ from the argument-initialized state and memory $\mu$ meets cost bound $T$ and postcondition $Q$, then the call to $p$ on those arguments meets the same bound and postcondition.

**Proof.** Use $s$ itself as the witness for the body of procedure $p$. The assumed lookup equation certifies that $s$ is that body, and the given execution and postcondition evidence are exactly what is required for the call to meet the bound. Together these witnesses establish the claim.
