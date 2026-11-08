<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.setIndicator_submodule_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Expansion of a Subspace Indicator

**Claim.** The indicator of $A$ is the function whose value at each $x$ is $2^{-\operatorname{codim}(A)}$ times the sum of the characters indexed by vectors perpendicular to $A$, evaluated at $x$.

**Proof.** Fix $x$. The pointwise subspace indicator formula gives exactly this equality at $x$ (`setIndicator_submodule_apply`). Since it holds for every $x$, the two functions are equal.

**Key facts.** `FABL.setIndicator_submodule_apply`.
