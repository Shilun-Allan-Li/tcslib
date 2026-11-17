<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.seg_callSegs_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Segment of a Call

**Claim.** Segment zero of a call's segment list is the initial segment selected by the call's mode from the input $x$.

**Proof.** By definition, the call's segment list begins with the segment selected by its mode from $x$. Looking up position zero in a list returns its head, so the result is exactly that initial segment.
