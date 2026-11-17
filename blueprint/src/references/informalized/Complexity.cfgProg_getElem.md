<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgProg_getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Program Entries

**Claim.** For every index within the configuration program, the entry at that index is the instruction constructed for that index.

**Proof.** By definition, the configuration program is the map of the instruction constructor over the range of valid indices. At an index within the program’s length, indexing this mapped range returns the mapped value at that index, namely the instruction constructed there.
