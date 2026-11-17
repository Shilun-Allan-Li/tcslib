<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.ext_getD' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality for Equal-Length Boolean Lists

**Claim.** Two Boolean lists of equal length are equal if their false-default entries agree at every index below that length.

**Proof.** The equal-length extensionality principle for lists (List.ext_getElem) reduces equality to checking corresponding entries at every valid index. Fix such an index. The assumed equality of false-default lookups applies there. Since the index is in range for both lists—the second range follows from equality of lengths—each defaulted lookup is the actual list entry. Thus the two entries agree at every position, proving the lists equal.
