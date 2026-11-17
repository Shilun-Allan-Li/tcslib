<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.clog_two_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling logarithm of two

**Claim.** The ceiling of the base-two logarithm of $2$ is $1$.

**Proof.** The ceiling logarithm fact `Nat.clog_eq_one` states that when the base is at least $2$ and is at most the argument, the ceiling logarithm equals one. Taking both base and argument to be $2$ meets these bounds, so the value is $1$.
