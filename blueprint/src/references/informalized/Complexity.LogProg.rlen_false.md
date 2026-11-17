<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.rlen_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of an Undoubled Segment

**Claim.** For every Boolean word $w$, the length assigned to $(w,\mathrm{false})$ is $|w|$.

**Proof.** By definition, the segment length is twice the word length when the flag is true and the ordinary word length when it is false. Substituting the false flag gives $|w|$.
