<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.lovaszSample_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncating a Lovász Sample

**Claim.** If $n^2k\le m$, then for every Boolean word $l$, the sample formed from its first $m$ bits agrees with the sample formed from all of $l$.

**Proof.** Compare the two samples at an arbitrary matrix position. Under the standard enumeration of the $n\times n$ positions, its index is less than $n^2$. Consequently the block of $k$ bits used there ends by position $(q+1)k\le n^2k\le m$, where $q$ is that index. Taking the first $m$ bits of $l$ therefore leaves this entire block unchanged. Its interpreted value, and thus the sample entry at the chosen position, is unchanged. Since this holds at every position, the samples agree.
