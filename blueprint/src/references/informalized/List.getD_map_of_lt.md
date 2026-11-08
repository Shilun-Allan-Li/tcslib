<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_map_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup commutes with mapping

**Claim.** At any in-range position in a finite list, looking up after mapping a function gives the function applied to the original lookup, regardless of the defaults.

**Proof.** Since the index is within the list length, defaulted lookup agrees with ordinary indexed access both in the original list and in its mapped list. Mapping preserves the list's length, and indexed access in a mapped list is the map applied to indexed access in the original list. Combining these facts gives the stated equality; the defaults are unused because the index is in range.
