<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.codeSigma_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of machine encoding

**Claim.** A binary-choice Turing machine with $k$ work tapes and state set $\\{0,\\ldots,s\}$ is determined by its tape count, state bound, initial state, and two transition functions; hence the map to this tuple is injective.

**Proof.** Take two machines whose encoded tuples agree. Equality of the outer dependent pairs first gives equality of their tape counts and state bounds. After identifying these parameters, equality of the remaining components gives equality of the initial states and of the transition functions. The two machine structures therefore agree in every field, so the machines are equal. This proves injectivity.
