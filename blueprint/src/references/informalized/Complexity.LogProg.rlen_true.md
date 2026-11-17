<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.rlen_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Doubled Segment

**Claim.** For every Boolean word $w$, the length assigned to the segment $(w,\mathrm{true})$ is $2|w|$.

**Proof.** By definition, the length of a segment is the length of its word doubled when its second component is true. Substituting $(w,\mathrm{true})$ therefore gives $2|w|$.
