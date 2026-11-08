<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.getD_map_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapping commutes with list lookup

**Claim.** For an index within a list’s length, applying a function to the default lookup equals default-false lookup in the mapped list.

**Proof.** Because the index is in range, each default lookup agrees with ordinary indexed lookup: this holds for the original list and for its mapped list. Lookup in a mapped list is the function applied to the original entry at that index. Combining these identities gives the equality.
