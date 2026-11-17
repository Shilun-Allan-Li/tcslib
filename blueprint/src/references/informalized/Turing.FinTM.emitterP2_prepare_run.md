<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Complete Preparation Run

**Claim.** For any Boolean words $w,s$, there is a time $t\le 5(|s|+|w|+3)$ at which the preparation machine reaches phase $8$, with candidate $s$, an empty second tape, the suffix of $w$ after its first $|s|$ symbols on the third tape, and the prescribed heads and overflow flag.

**Proof.** Set $v=w\mathbin{\mathrm{drop}}|s|$, let $o$ record whether $|w|<|s|$, and use the input-head position at the right boundary of $w$ for the intermediate frame. The proof concatenates five portions of the machine's run.

1. The candidate-copying result (`emitterP2_prepare_candidate`) runs for $|s|+1$ steps, copying $s$ onto the first two tapes and entering phase $1$. Since the copy is complete, this frame has the required flag and input-head position for the next portion.
2. The suffix-copying result (`emitterP2_prepare_suffix`) runs for $|v|+1$ steps to place $v$ on the third tape and enter phase $2$. At this boundary the input head is at the end of $w$, so the next transition advances to phase $3$ without moving the input head or changing the tapes.
3. That phase-$2$ transition also moves the first two work heads from $|s|$ to $|s|-1$. The candidate rewind result (`emitterP2_prepare_rewind_candidate`), applied with $j=|s|$, then takes $|s|+1$ steps to reach phase $4$ and return those two heads to zero.
4. The phase-$4$ transition moves the suffix head from $|v|$ to $|v|-1$ and enters phase $5$. The suffix rewind result (`emitterP2_prepare_rewind_suffix`), with $j=|v|$, takes $|v|+1$ further steps to reach phase $6$ and return that head to zero.
5. From phase $6$, the catalog rewind fact (`catalogRewind`) gives a run of some length $r\le |w|+3$ reaching phase $8$ with the input head returned to position $1$. The tapes and work-head positions are unchanged in this control-only scan.

The runs are concatenated using `emitterP2_join`, with the single transitions justified by `controlAction_apply` and the fact that a zero input movement fixes the input-head position (`moveInputPos_zero`). The copy and suffix steps use `bufferTape_nat` to identify the symbols read from the tapes. For the time bound, $|v|\le |w|$, so the total is at most
\[
(|s|+1)+(|v|+1)+(|s|+1)+(|v|+1)+(|w|+3)
\le 5(|s|+|w|+3).
\]
The final frame has the claimed words, phase, flag, and head positions.

**Key facts.** `Turing.FinTM.emitterP2_prepare_candidate`, `Turing.FinTM.emitterP2_prepare_suffix`, `Turing.FinTM.emitterP2_prepare_rewind_candidate`, `Turing.FinTM.emitterP2_prepare_rewind_suffix`, `Turing.FinTM.catalogRewind`, `Turing.FinTM.emitterP2_join`, `Turing.FinTM.controlAction_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
