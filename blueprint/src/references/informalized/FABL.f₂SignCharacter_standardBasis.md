<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.f₂SignCharacter_standardBasis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign character on a standard basis vector

**Claim.** For $\gamma\in\mathbb F_2^n$, the sign character associated with $\gamma$, evaluated at the $i$th standard basis vector, equals $\operatorname{signEncode}(\gamma_i)$.

**Proof.** The character evaluates to the encoding of the dot product of $\gamma$ with the standard basis vector. In that dot product, every coordinate except the $i$th contributes zero, while the $i$th contributes $\gamma_i\cdot 1=\gamma_i$. Thus the dot product is $\gamma_i$, and encoding it gives the claimed value.
