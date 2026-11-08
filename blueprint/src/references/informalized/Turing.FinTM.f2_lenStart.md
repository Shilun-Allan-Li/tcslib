<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenStart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the Pair-Scanning Computation

**Claim.** If $M$ computes $w$ from $x$ within $T$ steps, there is a halting configuration $c$ of $M$ with output $w$ and a time at most $T+|x|+4$ at which the augmented machine is positioned at the start of the input in its pair-reading state, with the original tapes as in $c$, the extra tape holding $w$ and its head at $|w|-1$, and empty output.

**Proof.** Choose the least time $t$ at which $M$ halts. Such a time exists by the computation hypothesis, and minimality gives $t\le T$ (`computesInTime_iff`). Let $c$ be the configuration at time $t$. It is halting, and its output equals $w$: the output-uniqueness theorem identifies it with the output of the given computation (`ComputesInTime.output_unique`). Up to time $t$, the augmented machine simulates $M$ while storing the output on its extra tape. The simulation identity for captured configurations applies because the original computation has not halted at any earlier time (`capture_run`). Thus at time $t$ the augmented machine is in the captured version of $c$. One more transition enters the rewind state while leaving the input-head position and original tape contents and positions unchanged; the extra tape now contains the stored output. The rewind lemma then returns the input head to the first position and enters the pair-reading state, in at most the current input position plus two steps (`f2_catalogRewind`). The configuration is exactly the required length-counting configuration: its extra-tape head is at $|c.output|-1$, and its output remains empty. Since $t\le T$ and the rewind takes at most $|x|+3$ steps from the position reached after the setup transition, the total is bounded by $T+|x|+4$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.capture_run`, `Turing.FinTM.f2_catalogRewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
