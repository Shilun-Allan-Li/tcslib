<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.booleanInfluence_comp_reorientInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Input Reorientation

**Claim.** Reorienting the inputs of a Boolean function by a fixed sign vector leaves its influence in each coordinate unchanged.

**Proof.** The reorientation map is a bijection of the finite sign cube, so changing variables by this map preserves the uniform average defining influence. Under this change of variables, an input is pivotal for the reoriented function exactly when its reorientation is pivotal for the original function: reorientation commutes with flipping coordinate $i$ (`FABL.reorientInput_flipCoordinate`). Hence the pivotal-event indicators correspond under the bijection, and their uniform averages, the two influences, are equal.

**Key facts.** `FABL.reorientInput_flipCoordinate`.
