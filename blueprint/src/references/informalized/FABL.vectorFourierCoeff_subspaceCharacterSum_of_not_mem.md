<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.vectorFourierCoeff_subspaceCharacterSum_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Vanishing Outside a Subspace

**Claim.** If $\gamma\notin H$, then the Fourier coefficient at $\gamma$ of the sum of Walsh characters indexed by elements of $H$ is zero.

**Proof.** Write the Fourier coefficient as the average of the subspace character sum times the Walsh character at $\gamma$, using the expectation formula (`FABL.vectorFourierCoeff_eq_expect`). Expand the subspace sum and interchange the finite sum with the average. By character orthogonality (`FABL.expect_vectorWalshCharacter_mul`), each resulting average is $1$ if the underlying vector $\beta$ equals $\gamma$, and $0$ otherwise. Equality is impossible: every $\beta\in H$ lies in $H$, whereas $\gamma\notin H$. Thus every summand vanishes, and so does the coefficient.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.expect_vectorWalshCharacter_mul`.
