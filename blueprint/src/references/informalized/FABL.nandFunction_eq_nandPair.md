<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.nandFunction_eq_nandPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-input NAND identity

**Claim.** For every two-coordinate input, the NAND function equals the two-input NAND operation applied to its coordinates.

**Proof.** Both sides are defined by the same condition: the output is $1$ exactly when the first and second coordinates are both $-1$, and is $-1$ otherwise. Thus the two expressions agree for every input.
