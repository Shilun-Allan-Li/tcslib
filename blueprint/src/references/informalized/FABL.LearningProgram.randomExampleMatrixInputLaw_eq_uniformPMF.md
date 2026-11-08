<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.randomExampleMatrixInputLaw_eq_uniformPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Law of Matrix Inputs

**Claim.** The probability mass function for the matrix of inputs indexed by $I$ and $\mathrm{Fin}(m)$ is the uniform probability mass function on all such matrices of $n$-dimensional sign vectors.

**Proof.** Unfold the matrix-input law and the uniform probability mass function. To show the two probability mass functions agree, compare their masses at an arbitrary matrix. In each case that mass is the uniform mass assigned to one element of the same finite, nonempty matrix space, so the masses agree for every matrix; hence the laws are equal.
