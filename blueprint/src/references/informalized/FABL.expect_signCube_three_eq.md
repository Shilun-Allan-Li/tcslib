<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.expect_signCube_three_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean on the Three-Dimensional Sign Cube

**Claim.** For every function $g$ on the three-dimensional sign cube, its uniform mean is the sum of its values over all triples of signs, divided by $8$.

**Proof.** The uniform mean on a finite set is the sum of the function's values divided by the set's cardinality. Reindex the sum over the cube by the equivalence between sign assignments on three coordinates and ordered triples of signs. Under this reindexing, each assignment corresponds to exactly one triple $(a,b,c)$, and the associated cube point is precisely `signCubeThreeOfSigns a b c`. Thus the sum over the cube is the iterated sum over $a,b,c$. Since there are two signs in each coordinate, the cube has $2^3=8$ elements, giving the stated formula.
