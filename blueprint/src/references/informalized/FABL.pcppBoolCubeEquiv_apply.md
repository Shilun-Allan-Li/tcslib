<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.pcppBoolCubeEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of the Boolean Cube Equivalence

**Claim.** For every Boolean vector $w$ of length $n$ and coordinate $i$, coordinate $i$ of its image in the $n$-dimensional cube over $\mathbb F_2$ is the image of $w_i$ under the standard Boolean-to-$\mathbb F_2$ equivalence.

**Proof.** The cube equivalence is defined coordinatewise by applying the Boolean-to-$\mathbb F_2$ equivalence in each coordinate. Evaluating its image at coordinate $i$ therefore gives the image of $w_i$, as claimed.
