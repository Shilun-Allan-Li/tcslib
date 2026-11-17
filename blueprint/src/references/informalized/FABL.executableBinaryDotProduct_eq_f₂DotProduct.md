<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableBinaryDotProduct_eq_f₂DotProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Executable Binary Dot Product

**Claim.** For binary vectors $a,b\in\mathbb F_2^\ell$, the executable binary dot product of $a$ and $b$ equals their dot product over $\mathbb F_2$.

**Proof.** The state recurrence sums the products of corresponding coefficients over indices below its step count, so at step $\ell$ the executable dot product is the sum over $j<\ell$ of the coefficient products. By the definition of the binary dot product, it is the sum over $i\in\mathrm{Fin}(\ell)$ of $a_i b_i$. For each such index, the coefficient accessor returns the corresponding vector entry, since $i<\ell$. Finally, the sum over $\mathrm{Fin}(\ell)$ is the same as the sum over the natural-number range $0\le j<\ell$. Thus the two expressions agree.

**Key facts.** `FABL.executableBinaryDotProductState_eq_sum`.
