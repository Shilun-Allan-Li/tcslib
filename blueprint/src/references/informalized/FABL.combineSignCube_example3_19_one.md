<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.combineSignCube_example3_19_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of a Free Coordinate

**Claim.** For any assignment of signs to the free coordinates 0 and 1, combining it with the specified fixed assignment gives the sign assigned by y at coordinate 1.

**Proof.** Regard coordinate 1 as an element of the free-coordinate set. The combination agrees with the free assignment at every such coordinate, by the free-coordinate evaluation property (`FABL.combineSignCube_apply_free`). Applying that property at coordinate 1 gives the claimed value.

**Key facts.** `FABL.combineSignCube_apply_free`.
