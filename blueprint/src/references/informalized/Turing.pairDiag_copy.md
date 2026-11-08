<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy-pass output and head position

**Claim.** Starting in the copy state on input $x$, with input head at position $1$ and output $w$, after $t\le |x|$ steps the machine remains in the copy state, its input head is at position $t+1$, and its output is $w$ followed by the first $t$ bits of $x$.

**Proof.** Induct on $t$. At $t=0$, the initial configuration already has the stated state, head position, and output. For the successor step, the induction hypothesis places the head at the position of the next bit $x[t]$. The input-symbol fact for this configuration (`pairDiag_inner`) identifies that bit, and the machine's one-step description (`pairDiag_step`) gives the copy transition: it stays in the copy state, emits the read bit, and moves the input head right. Since $t<|x|$, this move advances the head to position $t+2$ without reaching the right boundary (`moveInputPos_pos_of_ne_right`). The new output is $(w\mathbin{++}x.take(t))\mathbin{++}[x[t]]$, which is $w\mathbin{++}x.take(t+1)$. Configurations with zero work tapes are equal once their state, input position, and output agree (`Cfg.ext_zero_tapes`), completing the induction.

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.pairDiag_inner`, `Turing.pairDiag_step`.
