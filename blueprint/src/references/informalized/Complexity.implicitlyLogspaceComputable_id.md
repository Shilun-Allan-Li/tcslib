<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.implicitlyLogspaceComputable_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Implicit Logspace Computability of Identity

**Claim.** The identity function on finite bit strings is implicitly logspace computable.

**Proof.** For the identity function, the output length equals the input length, so it is bounded by $1\cdot(|x|+1)^1$. The two index languages required by the definition are the access languages for the identity output: one asks whether the indexed bit is $1$, and the other whether the index is below the output length. Both are in logarithmic space by the supplied access-language result (`access_mem`), applied to the bit and length modes respectively.

**Key facts.** `Complexity.LogProg.access_mem`.
