<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.expect_vectorWalshCharacter_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of vector Walsh characters

**Claim.** For indices $\beta$ and $\gamma$, the uniform expectation of the product of their vector Walsh characters is $1$ if $\beta=\gamma$, and $0$ otherwise.

**Proof.** Write each vector Walsh character as the binary Walsh character indexed by the support of its vector. The expectation of the product of two such characters is $1$ exactly when their supports agree, and is $0$ otherwise, by the binary Walsh product expectation formula (`expect_binaryWalshCharacter_mul`). If $\beta=\gamma$, their supports agree and the expectation is $1$. If the indices differ, their supports must differ, since the support encoding is injective (`f₂CubeEquivFinset`); the expectation is then $0.

**Key facts.** `FABL.expect_binaryWalshCharacter_mul`.
