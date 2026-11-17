<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The doubling pass

**Claim.** For every finite Boolean string $x$ and every $t\le |x|$, running the diagonal pairing machine from its initial configuration for $2t$ steps yields state $0$, input-head position $t+1$, and output consisting of the first $t$ bits of $x$, each repeated twice.

**Proof.** Induct on $t$. At $t=0$, the initial configuration has the stated state, position, and empty output. For the successor step, rewrite the time as two successive steps after time $2t$ and apply the induction hypothesis. The first step reads $x[t]$ (`pairDiag_inner`); the machine's transition description (`pairDiag_step`) shows that this step moves from state $0$ to state $1$, leaves the head in place, and emits nothing. The second step reads the same bit and transitions back to state $0$, emitting that bit and moving right. The head move advances from position $t+1$ to $t+2$, since $t<|x|$ (`moveInputPos_pos_of_ne_right`); the stationary move leaves the position unchanged (`moveInputPos_zero`). The two emitted copies extend the output from $(x.take(t)).flatMap\,(b\mapsto[b,b])$ to $(x.take(t+1)).flatMap\,(b\mapsto[b,b])$. Equality of the zero-work-tape configurations follows from agreement of their state, input position, and output (`Cfg.ext_zero_tapes`). The induction uses the run recursion that identifies each successor time with one additional machine step (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_zero`, `Turing.pairDiag_inner`, `Turing.pairDiag_step`.
