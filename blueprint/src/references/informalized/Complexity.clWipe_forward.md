<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clWipe_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Scan of the Scratch Tape

**Claim.** If the target head starts at $j\le |w|$ in control state $0$, then after $|w|-j+1$ steps the reset machine is in control state $1$, with target word $w$ and target head at $|w|-1$.

**Proof.** Induct on the remaining distance $|w|-j$, generalizing the starting position. If this distance is zero, then $j=|w|$: one transition enters control state $1$ and leaves the target word unchanged, with the head at $|w|-1$. If the distance is positive, then $j<|w|$, so cell $j$ contains the bit $w[j]$ (`Turing.FinTM.bufferTape_nat`). The next transition advances the target head to $j+1$, preserves the tape contents and stream, and keeps control state $0$. The run successor law expresses the full run as this transition followed by the remaining run (`Turing.MultiTapeTM.runFrom_succ_eq_step`); the induction hypothesis applies at $j+1$, since the remaining distance has decreased by one. The input head stays fixed at each transition by the zero-move law (`Turing.moveInputPos_zero`), and the zero-time run law resolves the endpoint case (`Turing.MultiTapeTM.runFrom_zero`).

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_zero`.
