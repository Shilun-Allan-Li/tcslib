<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrCfg_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Work Tape Preservation

**Claim.** In the assembled clock configuration, each right-block work tape of the clock scans the same symbol as the corresponding work tape in the configuration of $W$.

**Proof.** Fix a work-tape index $i$. The right block of the assembled tape contents is exactly the tape contents of $c$, and the right block of the assembled head positions is exactly the head positions of $c$. Evaluating the scanned symbol at the assembled head position therefore gives the symbol scanned by $c$ at its own head position. Since this holds for every $i$, the two functions of work-tape indices agree.
