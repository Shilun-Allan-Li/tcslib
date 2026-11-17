<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.seg_callSegs_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument Segments in a Call

**Claim.** For an argument position $a$ within a call specification's argument list, segment $a+1$ in the call's segment list is the word assigned to argument register $a$, paired with a flag that is true exactly when another argument follows.

**Proof.** The call's segment list consists of its mode-selected initial segment followed by the argument segments. Looking up position $a+1$ therefore drops the initial segment, by the successor lookup rule (`seg_cons_succ`). Apply the description of argument segments (`Complexity.LogProg.seg_argSegs`) to the mapped list of words assigned to the argument registers. Its length is the length of the argument list, and its word at position $a$ is the value assigned by $W$ to register $a$. Thus the resulting pair has the asserted word and flag.

**Key facts.** `Complexity.LogProg.seg_cons_succ`, `Complexity.LogProg.seg_argSegs`.
