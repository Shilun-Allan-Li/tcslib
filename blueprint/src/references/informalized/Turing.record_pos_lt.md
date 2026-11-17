<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.record_pos_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Width Bound

**Claim.** If $w$ is the length of the binary expansion of $n+1$, then $n+1<2^w$.

**Proof.** The binary digit length used to define $w$ is the binary size of $n+1$. The standard strict bound for a natural number in terms of its binary size states that a number is less than two raised to that size. Applying it to $n+1$ gives the claim.
