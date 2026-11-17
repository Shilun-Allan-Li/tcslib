<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.satisfiesLinearized_iff_mem_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearized Solutions as an Affine Subspace

**Claim.** If $a_0$ satisfies the linearized system, then a vector $a$ satisfies it exactly when it belongs to the affine subspace through $a_0$ directed by the solutions of the associated homogeneous linear system.

**Proof.** Membership in the affine subspace through $a_0$ with direction $H$ is equivalent to $a+a_0\in H$ (`FABL.mem_binaryAffineSubspace_iff_add_mem`), where $H$ is the set of vectors whose linearized equation values are all zero. Suppose first that $a$ satisfies the linearized system. For each equation, both its value at $a$ and its value at $a_0$ equal the right-hand side. Linearity makes its value at $a+a_0$ the sum of those two values, which is zero because every element of $\mathbb{F}_2$ added to itself is zero. Thus $a+a_0\in H$. Conversely, if $a+a_0\in H$, then for each equation its value at $a$ plus its value at $a_0$ is zero. Since $a_0$ has value equal to the right-hand side, this identity implies that the value at $a$ is also that right-hand side. Therefore $a$ satisfies the system.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`.
