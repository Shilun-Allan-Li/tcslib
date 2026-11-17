<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.tableauVertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tableau Vertex Lies Within the Next Block

**Claim.** For every index $j$ up to the snapshot width, the vertex assigned to index $j$ in time block $t$ lies strictly before the base of block $t+1$.

**Proof.** The embedding offset for an index within the gadget list is strictly less than the total embedding width (`embedOffset_lt`). Hence the vertex's index, which is the base at time $t$ plus that offset, is strictly less than the base plus the full tableau width. The next base adds exactly one tableau width to the current base, so this is precisely the desired strict bound.

**Key facts.** `BoolCircuit.embedOffset_lt`.
