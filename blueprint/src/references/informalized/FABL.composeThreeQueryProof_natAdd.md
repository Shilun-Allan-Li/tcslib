<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.composeThreeQueryProof_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary Proof Coordinates

**Claim.** At the added coordinate indexed by an auxiliary position $q$ and verifier seed $s$, the composed proof equals the Boolean encoding of the corresponding coordinate of the chosen local auxiliary witness.

**Proof.** The index formed from $q$ and the finite index of $s$ lies in the added-coordinate summand of the composed proof's index decomposition. The definition of the composed proof then returns the Boolean encoding of the local auxiliary witness at that position and at the seed recovered from its finite index. Since the finite indexing equivalence sends the index of $s$ back to $s$, this is the stated value.
