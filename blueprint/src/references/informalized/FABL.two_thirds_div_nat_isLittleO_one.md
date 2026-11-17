<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.two_thirds_div_nat_isLittleO_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A vanishing sequence

**Claim.** As $n$ tends to infinity through the natural numbers, $(2/3)/n$ is little-o of the constant sequence $1$, equivalently it tends to zero.

**Proof.** The sequence $3/n$ is little-o of the constant sequence $1$ (`three_div_nat_isLittleO_one`). Multiplication by a fixed scalar preserves little-o, so $(2/9)(3/n)$ has the same property. Since $(2/9)(3/n)=(2/3)/n$, the claimed sequence is little-o of $1$.

**Key facts.** `FABL.three_div_nat_isLittleO_one`.
