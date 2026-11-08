<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.flipAt_apply_same -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a flip at its coordinate

**Claim.** At coordinate $i$, the input obtained by flipping at $i$ has value equal to the negation of the original value there.

**Proof.** By definition, the flip replaces the value at coordinate $i$ by its negation. Evaluating the flipped input at that coordinate therefore gives $\neg x_i$.
