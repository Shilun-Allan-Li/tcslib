<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.lt_of_getD_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List Index Bound

**Claim.** If the defaulted value of a Boolean list $l$ at index $i$ is true, then $i<|l|$.

**Proof.** If $i$ were at least the length of $l$, then the optional lookup of $l$ at index $i$ would be absent. The defaulted lookup would therefore return the specified default, false, contradicting the hypothesis that it is true. Thus $i<|l|$.
