<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.convolution_completeQuadratic_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-convolution of a quadratic sign function

**Claim.** For even $n$, the self-convolution of the sign function defined by the complete quadratic form equals $1$ at zero and $0$ at every nonzero vector.

**Proof.** Write the convolution at $z$ as the uniform average of the product of the quadratic sign function at $y$ and its translate at $z+y$. The translation identity for the complete quadratic sign function rewrites this product as a fixed sign depending on $z$, multiplied by the Walsh character whose frequency is the polar frequency associated with $z$. The average of a Walsh character is $1$ at zero frequency and $0$ at every nonzero frequency (the character-average identity, `FABL.expect_vectorWalshCharacter`).

If $z=0$, its polar frequency is zero, and the product is identically $1$, so the convolution is $1$. If $z\ne0$, the polar frequency cannot be zero: for even $n$, vanishing of that frequency implies $z=0$ (`FABL.completeQuadraticPolarFrequency_eq_zero_of_even`). Thus the character has nonzero frequency and averages to zero; the fixed sign factor does not change that value.

**Key facts.** `FABL.convolution_apply_add`, `FABL.completeQuadratic_mul_translate`, `FABL.expect_vectorWalshCharacter`, `FABL.completeQuadraticPolarFrequency_eq_zero_of_even`.
