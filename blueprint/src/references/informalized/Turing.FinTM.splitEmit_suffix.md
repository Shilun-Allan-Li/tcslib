<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitEmit_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix copying by the split emitter

**Claim.** If $w=q r$, then starting in state $3$ at input position $|q|$, with counter position $h$ and output $o$, the emitter halts after $|r|+1$ steps at input position $|w|$, with the same work tapes and counter position and output $o r$.

**Proof.** Induct on the suffix $r$. If it is empty, the input head is at the end of $w$. The state-$3$ transition on the blank input emits nothing and halts, so the configuration is the claimed one after one step. For a nonempty suffix, write it as $b$ followed by a shorter suffix. The input head reads $b$; in state $3$ the machine emits $b$, advances the input head by one, and remains in state $3$. The counter and work tapes do not change. Apply the induction hypothesis to the remaining suffix, with the prefix extended by $b$ and the output extended by $b$. The resulting output is $o$ followed by the entire suffix, the head reaches the end of $w$, and the step count is $|r|+1$.

**Key facts.** `Turing.FinTM.splitPos_read`, `Turing.FinTM.splitPos_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
