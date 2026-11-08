<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.clog_two_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling logarithm of two

**Claim.** The least natural number $k$ such that $2\leq 2^k$ is $1$.

**Proof.** The defining characterization of the ceiling logarithm gives the value $1$ when the base is $2$ and the argument is $2$: the inequalities required for this case are both $2\leq 2$ (Nat.clog_eq_one).
