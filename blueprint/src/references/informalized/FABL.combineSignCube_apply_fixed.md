<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.combineSignCube_apply_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combined sign vector on fixed coordinates

**Claim.** At every index outside $J$, the sign vector formed by combining assignments on $J$ and its complement takes the value prescribed by the assignment on the complement.

**Proof.** The combined vector is defined by applying the inverse of the coordinate-splitting equivalence to the pair of assignments. At an index outside $J$, the inverse splitting equivalence recovers the complementary-coordinate component. Thus the value is the prescribed sign at that index.
