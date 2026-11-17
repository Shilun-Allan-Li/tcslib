<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.constantPairSubspace_one_eq_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The One-Dimensional Constant-Pair Subspace

**Claim.** In the one-dimensional vector space over $\mathbb F_2$, the subspace consisting of the zero vector and the all-ones vector is the whole space.

**Proof.** It suffices to show that every vector $x$ in the ambient space belongs to the constant-pair subspace, whose underlying set is $\{0,1\}$. The sole coordinate $x(0)$ is either $0$ or nonzero. In the latter case, since the only nonzero element of $\mathbb F_2$ is $1$, it equals $1$. A vector on the singleton coordinate set is determined by its value there, so in the two cases respectively $x=0$ or $x=1$. Hence every vector lies in the subspace, proving it is the whole space.
