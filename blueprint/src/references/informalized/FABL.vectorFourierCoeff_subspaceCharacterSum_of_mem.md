<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.vectorFourierCoeff_subspaceCharacterSum_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of a Subspace Character Sum

**Claim.** If $\gamma\in H$, then the Fourier coefficient at $\gamma$ of the function obtained by summing the Walsh characters indexed by elements of $H$ is $1$.

**Proof.** By the expectation formula for vector Fourier coefficients (`FABL.vectorFourierCoeff_eq_expect`), the coefficient is the average of the subspace character sum times the Walsh character at $\gamma$. Expand the sum and interchange its finite sum with the average. Each term is the average of the product of the Walsh character indexed by $\beta$ and the one indexed by $\gamma$. Character orthogonality (`FABL.expect_vectorWalshCharacter_mul`) says this average is $1$ when $\beta=\gamma$ and $0$ otherwise. Since $\gamma\in H$, exactly one subtype element $\beta\in H$ has underlying vector $\gamma$, so the resulting sum is $1$.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.expect_vectorWalshCharacter_mul`.
