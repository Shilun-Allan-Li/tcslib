<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.expect_subspaceCharacterSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a subspace character sum

**Claim.** For a linear subspace $H$ of $\mathbb F_2^n$, the uniform expectation of the sum of its characters is $1$.

**Proof.** Interchange the finite sum over $\gamma\in H$ with expectation over $x$. For each fixed $\gamma$, the expected value of its Walsh character is $1$ if $\gamma=0$ and $0$ otherwise (by `FABL.expect_vectorWalshCharacter`). Since a subspace contains the zero vector exactly once, summing these expectations gives $1$.

**Key facts.** `FABL.expect_vectorWalshCharacter`.
