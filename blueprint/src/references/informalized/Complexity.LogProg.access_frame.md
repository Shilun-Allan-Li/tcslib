<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Head Bounds

**Claim.** Replacing one tape’s contents and head position in a safe configuration, while setting the state to any access state, preserves the bounds on all four work-head positions provided the replacement position itself lies within those bounds.

**Proof.** Fix a work tape $j$. If $j=r$, its head position in the modified configuration is the replacement position $q$, which satisfies the required bounds by hypothesis. If $j\ne r$, the update leaves its head position unchanged, so its bounds follow from the original configuration’s safety. Since this applies to every tape, the modified configuration is safe.
