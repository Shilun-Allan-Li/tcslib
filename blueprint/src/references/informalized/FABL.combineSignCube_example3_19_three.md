<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.combineSignCube_example3_19_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Third Coordinate

**Claim.** For every assignment of signs to coordinates 0 and 1, the combined sign vector has value $-1$ at coordinate 3.

**Proof.** Coordinate 3 lies outside the free-coordinate set, so regard it as a fixed coordinate. The combination agrees there with the fixed assignment, by the fixed-coordinate evaluation property (`FABL.combineSignCube_apply_fixed`). The specified assignment evaluates to $-1$ at coordinate 3 (`FABL.example3_19FixedAssignment_three`), proving the claim.

**Key facts.** `FABL.combineSignCube_apply_fixed`, `FABL.example3_19FixedAssignment_three`.
