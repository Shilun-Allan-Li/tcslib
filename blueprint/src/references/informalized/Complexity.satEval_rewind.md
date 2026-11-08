<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate Tape Rewind

**Claim.** Under the stated transition rule, starting at certificate head position $n-1$ in state $q$ and running for $n+1$ steps reaches state $d$ with the certificate head at $0$, while preserving the input position and the saved work tapes.

**Proof.** We induct on $n$. When $n=0$, the certificate head is at $-1$, so it scans a blank cell (`Turing.FinTM.bufferTape_left`). The assumed transition rule therefore moves the head right and enters state $d$. The input head does not move, and the work tapes and output are unchanged; the resulting configuration is the required one, by the configuration calculation in `Complexity.satEvalAction_apply` and the fact that a zero input movement preserves position (`Turing.moveInputPos_zero`). For the induction step, write the starting position as $(n+1)-1$. Since $n+1\le |u|$, the scanned certificate cell contains $u[n]$. The transition rule moves left, leaves the control state at $q$, and preserves all other configuration data, so one step reaches the canonical configuration with head at $n-1$. The induction hypothesis applies there for the remaining $n+1$ steps and reaches the desired configuration at head position $0$. The run decomposition into its first step and remaining steps gives the claimed total of $n+2$ steps.

**Key facts.** `Complexity.satEvalCfg_work`, `Turing.FinTM.bufferTape_left`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`, `Complexity.satEvalAction_apply`.
