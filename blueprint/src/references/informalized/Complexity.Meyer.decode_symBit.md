<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.decode_symBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Optional Boolean Symbol

**Claim.** For every optional Boolean symbol $v$, the reconstruction that returns absence when the blank test is true and otherwise returns the symbol given by the one test equals $v$.

**Proof.** There are three possibilities. If $v$ is absent, the blank test is true, so the reconstruction is absent. If $v$ is false, the blank test is false and the one test is false, so the reconstruction is $\mathrm{some}(\mathrm{false})$. If $v$ is true, the blank test is false and the one test is true, so the reconstruction is $\mathrm{some}(\mathrm{true})$. In each case the reconstructed symbol is exactly $v$.
