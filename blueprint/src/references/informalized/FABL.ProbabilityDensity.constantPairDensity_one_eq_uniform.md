<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.constantPairDensity_one_eq_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity in Dimension One

**Claim.** On $\mathbb F_2^1$, the constant-pair density is identically $1$.

**Proof.** Fix a vector $x\in\mathbb F_2^1$. The one-dimensional constant-pair subspace is the whole space (\texttt{constantPairSubspace_one_eq_top}), so every vector belongs to it. By the pointwise formula for subset density (\texttt{subsetDensity_apply}), its value at $x$ is the reciprocal of the uniform probability of this subspace times its indicator at $x$. The indicator is $1$, and the subspace is the whole space, whose uniform probability is $1$. Thus the density takes value $1$ at every $x$.

**Key facts.** `FABL.ProbabilityDensity.constantPairSubspace_one_eq_top`, `FABL.subsetDensity_apply`.
