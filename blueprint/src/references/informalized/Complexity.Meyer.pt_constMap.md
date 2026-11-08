<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_constMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-word computation

**Claim.** For each bit $b$, the function sending a Boolean word $u$ to the word consisting of $|u|$ copies of $b$ is polynomial-time computable.

**Proof.** Apply the general finite-state transduction result to the one-state transducer that outputs $b$ on every input bit and remains in its sole state. Its transduction emits one copy of $b$ for each input symbol, so it produces exactly the required word.

**Key facts.** `Complexity.polyTimeComputable_transduce`.
