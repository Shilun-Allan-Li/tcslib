<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix product verification criterion

**Claim.** Let $n$ be a natural number, let $A,B,C'$ be $n\times n$ matrices over $\mathbb{F}_2$, and let $x\in\mathbb{F}_2^n$. The coordinate equalities $C'x=A(Bx)$ hold if and only if $(C'-AB)x=0$.

**Proof.** By the matrix-vector multiplication law for a product, $A(Bx)=(AB)x$. By distributivity of matrix-vector multiplication over subtraction, $(C'-AB)x=C'x-(AB)x$. In a module, a difference is zero exactly when its two terms are equal. Therefore the vector equation $(C'-AB)x=0$ is equivalent to $C'x=(AB)x=A(Bx)$. Equality of these vectors is equivalent to equality in every coordinate, giving the desired criterion.
