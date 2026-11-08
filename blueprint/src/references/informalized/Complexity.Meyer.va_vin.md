<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.va_vin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the auxiliary string

**Claim.** Applying the total second projection, then the total first projection, then the total second projection to the nested encoding recovers $a$.

**Proof.** The outer second projection decodes the inner encoding containing $\langle t,a\rangle$ and $\langle j,p\rangle$. Taking its first projection recovers $\langle t,a\rangle$, and taking that pair's second projection recovers $a$. Each recovery follows from decoding an encoded pair, which returns the original pair.
