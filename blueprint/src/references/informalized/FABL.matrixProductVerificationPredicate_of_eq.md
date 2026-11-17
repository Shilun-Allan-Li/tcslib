<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationPredicate_of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact products pass verification

**Claim.** Let $n$ be a natural number, let $A,B,C'$ be $n\times n$ matrices over $\mathbb{F}_2$, and suppose $C'=AB$. Then every $x\in\mathbb{F}_2^n$ satisfies the verification equalities in every coordinate.

**Proof.** Fix a coordinate $i$. Replacing $C'$ by $AB$ using the assumed equality, the left side of the verification equality becomes $((AB)x)_i$. The matrix product law gives $(AB)x=A(Bx)$, so this is exactly the right side in coordinate $i$. Since $i$ was arbitrary, the verification predicate holds.
