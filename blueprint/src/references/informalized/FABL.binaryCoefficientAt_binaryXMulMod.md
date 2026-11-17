<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryCoefficientAt_binaryXMulMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient After Multiplication by the Indeterminate

**Claim.** For positive $\ell$, the $d$th coefficient after multiplication by the indeterminate modulo the specified monic polynomial is the shifted coefficient plus the top coefficient times the extended polynomial coefficient at $d$.

**Proof.** Separate the degrees into three cases. If $d<\ell$, the coefficient of the vector after the operation is the sum of the shifted coefficient and the top coefficient multiplied by $m_d$, which is the extended polynomial coefficient at that degree. If $d=\ell$, the resulting coefficient is zero by the convention that coefficients beyond the vector length vanish; on the right, the shifted coefficient is the top coefficient and the extended polynomial coefficient is $1$, so their sum is zero in the field with two elements. Finally, if $d>\ell$, both the resulting coefficient and the extended polynomial coefficient at $d$ vanish. Since $d>0$, the shifted coefficient also vanishes because its index $d-1$ is at least $\ell$. Thus both sides are zero.
