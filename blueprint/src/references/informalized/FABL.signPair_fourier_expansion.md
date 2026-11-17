<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.signPair_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Expansion on Two Signs

**Claim.** Every function $H$ on pairs of signs has the stated expansion as a linear combination of $1$, the first sign, the second sign, and their product, with coefficients given by the four signed averages of its values.

**Proof.** Write $z=(z_1,z_2)$. Each coordinate is either $1$ or $-1$, so there are four cases. In each case, substituting those signs into the right-hand side makes the constant and signed terms combine to the corresponding value among $H(1,1)$, $H(1,-1)$, $H(-1,1)$, and $H(-1,-1)$. The resulting expressions simplify by collecting coefficients, establishing the formula in all four cases.
