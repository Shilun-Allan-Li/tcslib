<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Language.mem_P_iff_exists_isPUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# P-Uniform Circuit Characterization of P

**Claim.** A Boolean language belongs to polynomial time exactly when it is recognized by a fan-in-two circuit family that is polynomial-time uniform.

**Proof.** If $L$ belongs to polynomial time, `Language.exists_isPUniform_of_mem_P` supplies a polynomial-time-uniform, fan-in-two circuit family recognizing exactly $L. Conversely, given such a family, `Language.mem_P_of_isPUniform` shows that its recognized language belongs to polynomial time. Since that language is $L$, the result follows.

**Key facts.** `Language.exists_isPUniform_of_mem_P`, `Language.mem_P_of_isPUniform`.
