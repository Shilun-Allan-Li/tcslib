<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.allBinaryVectors_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct binary vectors

**Claim.** For every natural number $\ell$, the recursively defined list of vectors in $\mathbb{F}_2^\ell$ contains no repetitions.

**Proof.** Proceed by induction on $\ell$. When $\ell=0$, the list consists of the single zero vector, so it has no repetitions. For the induction step, the list in dimension $\ell+1$ is formed by adjoining a leading $0$ to each vector in the dimension-$\ell$ list, followed by adjoining a leading $1$ to each such vector. Within each block there are no repetitions: adjoining a fixed coordinate preserves distinctness, so the induction hypothesis applies to both blocks. The blocks are disjoint because a vector in the first has leading coordinate $0$, whereas one in the second has leading coordinate $1$; these are distinct in $\mathbb{F}_2$. Hence the concatenated list has no repetitions.
