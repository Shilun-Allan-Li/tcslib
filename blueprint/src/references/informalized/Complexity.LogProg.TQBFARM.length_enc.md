<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.length_enc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Encoded Formula

**Claim.** If $x$ is the pair encoding of $qs$ and the serialization of $\varphi$, then $2|qs|+2\leq |x|$.

**Proof.** The pair encoding has length $2|qs|+2+|\mathrm{serialize}(\varphi)|$ (`Turing.length_pairEncode`). The serialized formula has nonnegative length, so dropping that final summand gives the claimed lower bound.

**Key facts.** `Turing.length_pairEncode`.
