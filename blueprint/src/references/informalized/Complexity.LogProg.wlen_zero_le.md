<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.wlen_zero_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the First Call Segment

**Claim.** For any call specification, input bit string $x$, and register assignment $W$, the length of the first segment in the resulting call segments is at most the length of $x$.

**Proof.** The first segment of the call is the segment selected by the call's mode. If the mode is whole-input, its word is exactly $x$, so its length equals $|x|$. If the mode selects the unary prefix, its word is the initial run of true bits in $x$. Every prefix of a list has length at most that of the list, so this segment also has length at most $|x|$.

**Key facts.** `Complexity.LogProg.seg_callSegs_zero`.
