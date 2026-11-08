<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableSmallBiasOutputBitWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Bit Work Identity

**Claim.** For every pair of natural numbers $\ell,j$, the work required for output bit $j$ is $\ell+(j+1)(M(\ell)+1)+2\ell+1$, where $M(\ell)$ is the work for one binary modular multiplication.

**Proof.** The output-bit work is the power-computation work for exponent $j+1$, plus the dot-product work and one final unit. The power-work identity (FABL.executableSmallBiasPowerWork_eq) evaluates the first term as $\ell+(j+1)(M(\ell)+1)$, and the dot-product-work identity (FABL.executableBinaryDotProductWork_eq) evaluates the second as $2\ell$. Combining these terms with the final unit gives the claimed expression.

**Key facts.** `FABL.executableSmallBiasPowerWork_eq`, `FABL.executableBinaryDotProductWork_eq`.
