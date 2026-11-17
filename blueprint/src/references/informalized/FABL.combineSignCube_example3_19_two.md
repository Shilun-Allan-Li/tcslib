<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.combineSignCube_example3_19_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Second Coordinate

**Claim.** For every assignment of signs to coordinates 0 and 1, the combined sign vector has value $1$ at coordinate 2.

**Proof.** Coordinate 2 is outside the free-coordinate set, hence is a fixed coordinate. The fixed-coordinate evaluation property says that the combined vector there equals the fixed assignment (`FABL.combineSignCube_apply_fixed`). At coordinate 2 that assignment has value $1$ (`FABL.example3_19FixedAssignment_two`), as required.

**Key facts.** `FABL.combineSignCube_apply_fixed`, `FABL.example3_19FixedAssignment_two`.
