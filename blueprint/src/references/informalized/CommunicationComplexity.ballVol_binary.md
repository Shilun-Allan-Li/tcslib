<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.ballVol_binary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Ball Volume Formula

**Claim.** For a binary alphabet, the ball volume is the partial sum of binomial coefficients from zero through t.

**Proof.** Substitute q=2 into the definition of ball volume. Each factor $(q-1)^i$ becomes $1^i=1$, so the summands reduce to the binomial coefficients, giving the stated partial sum.
