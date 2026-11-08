<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.segDbl_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling Flag of a Call Segment

**Claim.** For every valid segment index $s$, the flag computed by the call specification equals the second component of segment $s$ in the call's segment list.

**Proof.** Split on whether $s=0$. At zero, the segment list begins with the mode's initial segment, whose flag is true exactly in whole-input mode; this is precisely the definition of the computed flag. Otherwise write $s=a+1$. The index bound gives $a<|\mathrm{args}|$. The segment-list formula at this positive index says its flag is true exactly when $a+1<|\mathrm{args}|$, matching the computed flag at $s=a+1$.

**Key facts.** `Complexity.LogProg.seg_callSegs_zero`, `Complexity.LogProg.seg_callSegs_succ`.
