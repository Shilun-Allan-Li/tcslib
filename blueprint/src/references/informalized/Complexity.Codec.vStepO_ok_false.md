<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.vStepO_ok_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence of a False Validity Flag

**Claim.** If the validity flag of a verifier state is false, then after applying the option-valued verifier step to any optional cell, that flag remains false.

**Proof.** There are two cases. If no cell is supplied, the option-valued step leaves the other state data unchanged and explicitly sets the validity flag to false. If a cell is supplied, the step updates that flag by conjoining its previous value with further conditions. Since the previous value is false, the conjunction remains false.
