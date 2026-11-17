<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.subspaceEvaluationCharacter_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triviality of the Restricted Character

**Claim.** The character on $H$ obtained by evaluating each vector's Walsh character at $x$ is trivial if and only if $x$ is orthogonal to $H$ under the standard dot product over $\mathbb{F}_2$.

**Proof.** Suppose first that the restricted character is trivial. For each $\gamma\in H$, its value at $\gamma$ is therefore $1$. By the formula for evaluating a vector Walsh character (`vectorWalshCharacter_apply`), this says that the binary sign of the dot product of $\gamma$ and $x$ is $1$. The binary sign equals $1$ exactly at zero (`binarySign_eq_one_iff`), so every such dot product vanishes. The orthogonality criterion (`mem_perpendicularSubspace_iff`) then gives $x\in H^\perp$. Conversely, if $x\in H^\perp$, that same criterion makes the dot product of every $\gamma\in H$ with $x$ zero. The Walsh-character evaluation formula then gives value $1$ for every $\gamma\in H$, so the restricted character is trivial.

**Key facts.** `FABL.mem_perpendicularSubspace_iff`, `FABL.vectorWalshCharacter_apply`, `FABL.binarySign_eq_one_iff`.
