<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBoolean_isSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the quadratic Boolean function

**Claim.** The complete quadratic Boolean function is invariant under every permutation of its sign coordinates.

**Proof.** Fix a coordinate permutation and an input. Applying the inverse binary encoding coordinatewise to the permuted input gives the binary vector obtained by permuting the inverse encoding of the original input. Indeed, the encoding equivalence recovers each coordinate, and its coordinate formula is sign encoding ( `binaryCubeSignEquiv_apply`). The complete quadratic bit is invariant under this permutation of binary coordinates ( `completeQuadraticBit_comp_perm`). Encoding the resulting equal bits as signs therefore gives the same output, proving symmetry.

**Key facts.** `FABL.binaryCubeSignEquiv_apply`, `FABL.completeQuadraticBit_comp_perm`.
