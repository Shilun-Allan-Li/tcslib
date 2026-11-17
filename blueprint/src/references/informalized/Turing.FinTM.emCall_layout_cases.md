<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_layout_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Classification of call-layout indices

**Claim.** Every physical tape index in the prepared call layout is either the argument slot, the capture slot, or the slot for one source tape and one of its three tracked components: data, visited marks, or origin marks.

**Proof.** The layout has indices from $0$ through $1+3k$, where $k$ is the number of source tapes. If $j=0$, it is the argument slot. If $j=1+3k$, it is the capture slot. Otherwise, $j$ lies among the three consecutive blocks of $k$ tracked slots. In the first block, write $j=1+i$; in the second, write $j=1+k+i$; in the third, write $j=1+2k+i$. The bounds on $j$ in each case give $0\le i<k$, so $i$ is a source tape index, and the block identifies the corresponding component. This exhausts the layout.
