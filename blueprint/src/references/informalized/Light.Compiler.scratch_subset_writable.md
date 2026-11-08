<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.scratch_subset_writable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch Addresses Are Writable

**Claim.** Every address in the scratch set for $Z$ belongs to the writable-address set for $Z$ at stack index $q$.

**Proof.** The writable set is defined as a union whose first component is precisely the scratch set. Thus every scratch address belongs to that first component, and hence to the full writable set by inclusion into a union.
