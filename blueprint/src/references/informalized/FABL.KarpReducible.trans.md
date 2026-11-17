<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.KarpReducible.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Karp Reducibility

**Claim.** If the first language is Karp reducible to the second and the second to the third, then the first is Karp reducible to the third.

**Proof.** Let $f$ witness the reduction from the first language to the second, and let $g$ witness the reduction from the second to the third. Their composition $g\circ f$ is polynomial-time computable, since polynomial-time maps are closed under composition. For every input, membership in the first language is equivalent to membership of its image under $f$ in the second, which in turn is equivalent to membership of its image under $g\circ f$ in the third. Hence the composition witnesses the claimed reduction.
