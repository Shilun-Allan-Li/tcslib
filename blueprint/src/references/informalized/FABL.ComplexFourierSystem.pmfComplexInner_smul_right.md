<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.ComplexFourierSystem.pmfComplexInner_smul_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity in the second argument

**Claim.** The probability-weighted complex inner product is linear in its second argument: multiplying the second function by $c$ multiplies the inner product by $c$.

**Proof.** Expand the inner product as a finite sum and substitute $(cg)(x)=c g(x)$. In each summand, associativity and commutativity of complex multiplication move the factor $c$ outside the summand. Factoring it out of the finite sum gives $\langle f,cg\rangle_p=c\langle f,g\rangle_p$.
