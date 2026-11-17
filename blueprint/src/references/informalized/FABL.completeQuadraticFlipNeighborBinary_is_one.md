<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticFlipNeighborBinary_is_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic value after a coordinate repair

**Claim.** For $n\ge2$, the prescribed repair of any vector in $\mathbb F_2^n$ produces a vector whose complete quadratic bit is $1$.

**Proof.** Split according to the initial quadratic bit. If it is already $1$, the repair leaves the vector unchanged. If it is $0$ and some coordinate $i$ has derivative bit $1$, flipping that coordinate changes the quadratic bit by the product of the flip amount and that derivative (`completeQuadraticBit_add_single`), so the new value is $0+1=1$. In the remaining case, every derivative bit is different from $1$, hence is $0$ because the field has just two elements (`f₂_eq_zero_of_ne_one`). The repair flips coordinates $0$ and $1$, which are distinct since $n\ge2$. The formula for flipping two distinct coordinates adds both derivative bits and an additional $1$ to the original quadratic bit (`completeQuadraticBit_add_two_single`). All three prior terms are zero, so the result is $1$.

**Key facts.** `FABL.completeQuadraticBit_add_single`, `FABL.f₂_eq_zero_of_ne_one`, `FABL.completeQuadraticBit_add_two_single`.
