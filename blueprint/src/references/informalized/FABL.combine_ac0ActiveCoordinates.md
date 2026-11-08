<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.combine_ac0ActiveCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Active Coordinates

**Claim.** For m at least 7, placing y on the active coordinates and assigning +1 elsewhere yields a vector whose value at each indexed active coordinate is y at the corresponding original index.

**Proof.** The active-coordinate count is at most the ambient dimension, by the bound $2m^2\le 2^m$ for $m\ge7$ (`FABL.activeCoordinateCount_le_dimension`). Thus each index i of y determines an ambient active coordinate, and hence an element j of the active-coordinate set. The combination agrees with its free assignment at j, by the free-coordinate evaluation property (`FABL.combineSignCube_apply_free`). That free assignment is y reindexed along the bijection from the original indices to active coordinates, so its value at j is y at the inverse image of j. By construction, j is the image of i; the inverse image is therefore i, and the value is y(i).

**Key facts.** `FABL.activeCoordinateCount_le_dimension`, `FABL.combineSignCube_apply_free`.
