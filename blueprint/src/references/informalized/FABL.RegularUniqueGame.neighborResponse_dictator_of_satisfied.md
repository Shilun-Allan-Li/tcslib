<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.neighborResponse_dictator_of_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Response on a Satisfied Constraint

**Claim.** When the constraint permutation sends the neighbor’s assigned coordinate to the vertex’s assigned coordinate, the neighbor response of the dictator code at the query equals the dictator response at the vertex.

**Proof.** By definition, the neighbor response evaluates the dictator at the neighboring vertex on the permuted query. The dictator code there uses the coordinate assigned to that neighbor, so this response is the original query evaluated at the image of that coordinate under the constraint permutation. The satisfaction hypothesis identifies this image with the coordinate assigned to the vertex. The result is therefore exactly the dictator response at the vertex.
