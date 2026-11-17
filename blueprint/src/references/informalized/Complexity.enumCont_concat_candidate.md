<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_concat_candidate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Phase of Assembly

**Claim.** If $s=\mathit{pre}\mathbin{++}\mathit{rest}$, then after exactly $|\mathit{rest}|+1$ steps from candidate phase with candidate tape $s$ headed at $|\mathit{pre}|$ and output $\mathit{out}\mathbin{++}\mathit{pre}$, the machine is halted with the tape and head unchanged at the end of $s$ and output $\mathit{out}\mathbin{++}s$.

**Proof.** Proceed by induction on the remaining suffix, allowing the prefix to vary so that each induction step can absorb the next symbol. If the suffix is empty, then $s=\mathit{pre}$. The single prescribed candidate-phase step halts, leaves the candidate tape unchanged, keeps the input head fixed, and leaves the output as $\mathit{out}\mathbin{++}\mathit{pre}=\mathit{out}\mathbin{++}s$. If the suffix begins with a symbol $b$, the candidate head is at the beginning of that suffix, so it reads $b$. The machine outputs this symbol and advances the candidate-tape head one cell, without changing the tape or input head. Thus after one step the configuration is the same candidate-phase form with prefix $\mathit{pre}\mathbin{++}[b]$ and output $\mathit{out}\mathbin{++}(\mathit{pre}\mathbin{++}[b])$. The remaining suffix is shorter, and the induction hypothesis completes the assembly in its length plus one further steps. Altogether the run takes $|\mathit{rest}|+1$ steps, halts, and has output $\mathit{out}\mathbin{++}s$. The run iteration identities (`Turing.MultiTapeTM.runFrom_succ_eq_step` and `Turing.MultiTapeTM.runFrom_succ_eq_step'`) express these successive steps, while the base case uses the zero-run identity (`Turing.MultiTapeTM.runFrom_zero`); the candidate transition's effect is given by the control-action application identity (`Turing.FinTM.controlAction_apply`) and the natural-position buffer lookup (`Turing.FinTM.bufferTape_nat`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.controlAction_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
