<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationPredicate_imp_row_dot_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verified rows annihilate the test vector

**Claim.** Let $n$ be a natural number, let $A,B,C'$ be $n\times n$ matrices over $\mathbb{F}_2$, and let $x\in\mathbb{F}_2^n$. If $C'x=A(Bx)$ in every coordinate, then each row of $C'-AB$ has dot product zero with $x$.

**Proof.** The matrix product verification criterion says that acceptance is equivalent to the vector equation $(C'-AB)x=0$ (\texttt{FABL.matrixProductVerificationPredicate\_iff\_difference\_mulVec\_eq\_zero}). The dot product of row $i$ of a matrix with $x$ is the $i$th coordinate of its matrix-vector product (\texttt{FABL.f₂DotProduct\_matrixProductDifferenceRow}). Applying this to $C'-AB$, that dot product is the $i$th coordinate of the zero vector, hence is zero.

**Key facts.** `FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero`, `FABL.f₂DotProduct_matrixProductDifferenceRow`.
