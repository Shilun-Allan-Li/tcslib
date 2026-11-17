<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.frame_append_zeros -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending zeros preserves the frame

**Claim.** Appending any finite number of zeros to a list of integers leaves its frame unchanged at every index.

**Proof.** Fix an index $y$. The frame reads the list entry at $y$, returning zero when that entry is out of range. If $y$ is within the original list, concatenation leaves that entry unchanged. If it is beyond the original list, then either it lies in the appended block, whose entries are all zero, or it is beyond the concatenated list as well; in both cases the frame value is zero. Thus the two frames agree at every index, hence are equal as functions.
