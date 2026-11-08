<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_concat_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Phase of Assembly

**Claim.** If $x=\mathit{pre}\mathbin{++}\mathit{rest}$, then after exactly $|\mathit{rest}|+1$ steps from input phase with input head at $|\mathit{pre}|+1$, candidate tape $s$ headed at zero, and output $\mathit{pre}$, the machine is in candidate phase at the right boundary, with tape and head unchanged and output $x$.

**Proof.** Induct on the remaining input suffix, allowing the consumed prefix to grow. When the suffix is empty, the input head is at the right boundary, where the input symbol is blank. The machine switches from input phase to candidate phase in one step, leaving the candidate tape and output unchanged and keeping the input head at the boundary. Since $x=\mathit{pre}$, the output is $x$. If the suffix begins with $b$, the input head reads $b$ (`Turing.FinTM.inputSymbol_at`). The input-phase transition outputs $b$ and advances the input head by one while leaving the candidate tape unchanged. The resulting configuration has consumed prefix $\mathit{pre}\mathbin{++}[b]$ and the rest of the suffix remains; apply the induction hypothesis to it. This gives the stated total of $|\mathit{rest}|+1$ steps. The run iteration identities (`Turing.MultiTapeTM.runFrom_succ_eq_step` and `Turing.MultiTapeTM.runFrom_succ_eq_step'`) organize the recursive step and base case, and the control-action application identity (`Turing.FinTM.controlAction_apply`) describes the terminal phase switch; the input-head position updates use `Turing.moveInputPos_pos_of_ne_right` and `Turing.moveInputPos_zero`.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
