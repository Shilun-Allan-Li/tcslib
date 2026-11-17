<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.combineSignCube_improvedFKNFreeCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head and Tail of the Combined Vector

**Claim.** Combining the reindexed signs of x on the free coordinates with the fixed assignment z at coordinate 0 produces the vector whose head is z(0) and whose tail is x.

**Proof.** We prove equality of the two vectors by checking each coordinate, separating the head from the tail. At the head, coordinate 0 is fixed; the combination therefore has value z at the distinguished fixed index, by the fixed-coordinate evaluation property (`FABL.combineSignCube_apply_fixed`). This is the head value of the stated cons vector. For a tail coordinate indexed by i, its successor is free. The combination there equals the free assignment at the corresponding free index, by the free-coordinate evaluation property (`FABL.combineSignCube_apply_free`). By the definition of the reindexing, that value is x(i); the cons vector also has value x(i) at this successor coordinate. Thus the vectors agree at the head and at every tail coordinate, so they are equal.

**Key facts.** `FABL.combineSignCube_apply_fixed`, `FABL.combineSignCube_apply_free`.
