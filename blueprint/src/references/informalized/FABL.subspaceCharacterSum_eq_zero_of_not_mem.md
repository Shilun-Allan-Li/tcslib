<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.subspaceCharacterSum_eq_zero_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Sum Vanishes Outside the Orthogonal Subspace

**Claim.** For a subspace $H$ and a vector $x$ outside its orthogonal subspace, the sum over $H$ of the character obtained by evaluating each vector's Walsh character at $x$ is zero.

**Proof.** A finite group's character sum is zero whenever the character is nontrivial: this is the character orthogonality relation (the finite character sum formula `AddChar.sum_eq_ite`). Here, the character on $H$ is trivial exactly when its value, viewed as an additive character, is zero. The characterization `subspaceEvaluationCharacter_eq_zero_iff` says this happens exactly when $x$ is orthogonal to $H$. Since $x$ lies outside that orthogonal subspace, the character is nontrivial, and its sum over $H$ therefore vanishes.

**Key facts.** `FABL.subspaceEvaluationCharacter_eq_zero_iff`.
