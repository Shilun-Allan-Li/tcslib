<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlock_ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blocks Determined by Their Slices

**Claim.** Two blocks of the specified length are equal if their state slices, input-symbol slices, and every work-symbol slice agree.

**Proof.** To prove equality of the blocks, compare their bits at an arbitrary index. The index lies either in the state-code segment or in the remaining segment. In the latter, split again between the input-symbol segment and the work-symbol segment. In the first two cases, equality follows directly from the assumed equality of the corresponding slices. In the work-symbol segment, write the local index as twice a tape index plus a bit index, using quotient and remainder on division by two. The assumed equality of that tape's work-symbol slices gives equality at this bit. Thus the blocks agree at every index and are equal.
