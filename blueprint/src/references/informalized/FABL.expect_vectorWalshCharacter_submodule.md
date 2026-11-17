<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.expect_vectorWalshCharacter_submodule -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Walsh character on a subspace

**Claim.** The average over a linear subspace $H$ of the Walsh character indexed by $\gamma$ equals $1$ if $\gamma$ is orthogonal to every vector in $H$, and equals $0$ otherwise.

**Proof.** On $H$, the character indexed by $\gamma$ agrees with the evaluation character indexed by $\gamma$: the two evaluations are equal because the standard dot product is symmetric. The average of a character on a finite group is $1$ when the character is trivial and $0$ otherwise (`AddChar.expect_eq_ite`). The evaluation character is trivial exactly when $\gamma$ belongs to the perpendicular subspace (`subspaceEvaluationCharacter_eq_zero_iff`). Combining these facts gives the stated alternatives.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.subspaceEvaluationCharacter_eq_zero_iff`.
