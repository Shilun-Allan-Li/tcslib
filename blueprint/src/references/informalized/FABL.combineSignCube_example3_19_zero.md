<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.combineSignCube_example3_19_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Coordinate Zero

**Claim.** For every assignment of signs to the free coordinates 0 and 1, the combined vector has at coordinate 0 the sign assigned by y there.

**Proof.** Coordinate 0 is an element of the free-coordinate set. The combination agrees with the free assignment at each free coordinate, by the free-coordinate evaluation property (`FABL.combineSignCube_apply_free`). Evaluating that property at coordinate 0 gives the assertion.

**Key facts.** `FABL.combineSignCube_apply_free`.
