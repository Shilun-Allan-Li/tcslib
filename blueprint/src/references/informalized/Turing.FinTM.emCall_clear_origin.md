<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_clear_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Rewind to the Origin

**Claim.** Starting in state $2$ at head position $n$, with only the origin marker present, the cleaner reaches state $3$ with all tapes blank and all heads at the origin after exactly $n+1$ steps.

**Proof.** Induct on $n$. At $n=0$, the head is already at the origin. The state-$2$ transition sees the origin marker, erases it, and enters state $3$ without moving any head. The origin-erasure identity `emCall_origin_erase` says the resulting origin tape is blank everywhere; the data and interval tapes were already blank. For the successor case, the origin marker at position $n+1$ is blank, since the marker is supported only at zero (`bufferTape_nat`). In state $2$ the cleaner therefore moves one cell left and stays in state $2$. The remaining $n+1$ steps are the induction-hypothesis run from position $n$, by the run decomposition `runFrom_succ_eq_step`. The input position stays fixed because these transitions do not move the input head (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.emCall_origin_erase`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`.
