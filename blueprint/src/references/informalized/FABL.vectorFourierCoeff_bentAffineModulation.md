<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorFourierCoeff_bentAffineModulation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Under Affine Modulation

**Claim.** Multiplying a function by a fixed sign and a Walsh character shifts its vector Fourier coefficient at $\gamma$ to the coefficient of the original function at $a+\gamma$, multiplied by that sign.

**Proof.** The modulated function can be written as the fixed scalar $\operatorname{signValue}(\sigma)$ times the product of the Walsh character at $a$ with $f$. Pulling a constant scalar out of a Fourier coefficient (`vectorFourierCoeff_const_mul`) contributes that same scalar. Multiplication by the Walsh character at $a$ shifts the frequency from $\gamma$ to $a+\gamma$ (`vectorFourierCoeff_vectorWalshCharacter_mul`). Together these give the claimed identity.

**Key facts.** `FABL.vectorFourierCoeff_const_mul`, `FABL.vectorFourierCoeff_vectorWalshCharacter_mul`.
