<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding to the replay position

**Claim.** For every $j\le |a|$, starting in state $2$ with $a$ on the work tape, head at $j-1$, and empty output, after $j+1$ steps the machine is in state $3$ with its head at $0$, preserving the input position, tape, and empty output.

**Proof.** Induct on $j$. When $j=0$, the head is at $-1$ and reads no symbol (`bufferTape_left`). The state-$2$ transition moves the head to zero and enters state $3$, without changing the input position, tape, or output. For the successor case, the initial head position is $(j+1)-1=j$. Because $j<|a|$, it scans the $j$th bit (`bufferTape_nat`). In state $2$ the transition moves left and stays in state $2$, producing the configuration whose head is at $j-1$. The induction hypothesis now completes the remaining $j+1$ steps. The run recurrence (`runFrom_succ_eq_step`) expresses this first transition followed by those remaining steps; zero input movement preserves the input position (`moveInputPos_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
