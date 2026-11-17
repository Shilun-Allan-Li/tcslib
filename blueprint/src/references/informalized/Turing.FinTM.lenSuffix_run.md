<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenSuffix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix Length Comparison

**Claim.** For every decomposition $x=ps$ and $r\le |c.output|$, the checker started in its suffix-comparison state at position $|p|$ halts within $|s|+1$ steps, outputting the single bit that indicates whether $|s|\le r$.

**Proof.** Induct on the suffix $s$. If it is empty, the checker sees the end of input and halts with output $1$, which is the correct test for $0\le r$. If $s=b s'$ and $r=0$, it halts after one step with output $0$, since a nonempty suffix cannot have length at most zero. If $r=r'+1$, the checker reads $b$ and advances one input position while decrementing the counter to $r'$. The output buffer represents the simulated output, and its entry at counter index $r'$ is available because $r\le |c.output|$; thus the transition is the stated decrement-and-advance action (`lenAction_apply`). Apply the induction hypothesis to the remaining suffix $s'$ with counter $r'$. Composing this first step with the resulting run (`runFrom_add`) yields a halted configuration and output testing $|s'|\le r'$, equivalent to $|s|\le r$. The successor-time run identities (`runFrom_succ_eq_step` and `runFrom_zero`) express this composition, while the input-head movement advances to the next position (`moveInputPos_pos_of_ne_right`). The bound is $1+(|s'|+1)=|s|+1$.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.lenCfg_read`, `Turing.FinTM.lenAction_apply`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
