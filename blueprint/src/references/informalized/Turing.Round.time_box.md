<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Round.time_box -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Positions Remain Within a Time Box

**Claim.** Any round of duration $t$ also satisfies the head-position condition that, at every time $u\le t$, each work-tape head lies between its initial position minus $t$ and its initial position plus $t$, inclusive.

**Proof.** Keep the start, endpoint, and intermediate-state conditions of the given round. For each $u\le t$ and each tape $j$, the general head-displacement bound (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`) places the head at time $u$ in the interval from its initial position minus $u$ to its initial position plus $u$. Since $u\le t$, these bounds imply that the position also lies between the initial position minus $t$ and plus $t$. Thus the required head box holds throughout the round.

**Key facts.** `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`.
