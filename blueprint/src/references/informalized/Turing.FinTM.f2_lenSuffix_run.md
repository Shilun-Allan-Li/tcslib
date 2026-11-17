<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenSuffix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After Checking a Suffix Length

**Claim.** For every decomposition $x=uv$ and every $r\le |c.output|$, the augmented machine started in state $3$ at the beginning of $v$ halts within $|v|+1$ steps and outputs the single bit indicating whether $|v|\le r$.

**Proof.** Induct on the suffix $v$. If it is empty, the machine reads the end marker, emits true, and halts in one step; the end-of-input symbol is identified by the input-position formula (`f2_lenCfg_read`). Now suppose $v=b::v'$ and split into cases on $r$. If $r=0$, the extra-tape head is at position $-1$, where the buffered tape is blank (`bufferTape_left`). The state-$3$ transition therefore emits false and halts, as required because a nonempty suffix cannot have length at most zero. If $r=r'+1$, the head reads the corresponding stored output bit and the transition advances one input position while moving the extra-tape head back one cell. This gives the state-$3$ configuration at the start of $v'$ with counter $r'$ (`f2_lenAction_apply`); the scanned input bit and tape symbol are identified by the configuration read facts and the buffered-tape contents (`f2_lenCfg_read`). Apply the induction hypothesis to $v'$ and $r'$. The execution laws split this run into its first step and the remaining run (`runFrom_add`, `runFrom_succ_eq_step`, `runFrom_zero`), so its total length is at most $1+(|v'|+1)=|v|+1$.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.f2_lenAction_apply`, `Turing.FinTM.f2_lenCfg_read`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
