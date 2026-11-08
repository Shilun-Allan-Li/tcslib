<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the remaining suffix

**Claim.** Whenever $x=p++r$, the suffix-extraction machine started in state $5$ at the clamped offset $|p|$, with counter length $n$, counter head at $n$, and output $o$, reaches after $|r|+1$ steps the halting configuration at the clamped offset $|x|$, with the same counter and head and output $o++r$.

**Proof.** Induct on the suffix $r$. If $r$ is empty, the hypothesis $x=p++r$ identifies $x$ with $p$. The machine is already at the end of the input, so its next transition halts without moving the input head or counter head, changing the counter, or adding output. This gives the stated endpoint after one step.

For the inductive case write $r=b::r'$. At the current offset $|p|$, the input symbol is $b$; the state-$5$ transition advances the clamped input position by one and appends $b$ to the output, leaving the counter and its head unchanged. The remaining input has decomposition $x=(p++[b])++r'$. Apply the induction hypothesis from the resulting state-$5$ configuration: in $|r'|+1$ further steps it halts at the clamped end of $x$ and appends $r'$ to the current output. Together with the first step, this takes $|r|+1$ steps and produces $o++[b]++r'=o++r$. The transition description used here is Complexity.satDrop_move; the input-symbol and position facts are Complexity.satStreamPos_read, Complexity.satStreamPos_succ, and Turing.moveInputPos_zero, with the run-step decomposition supplied by Turing.MultiTapeTM.runFrom_succ_eq_step.

**Key facts.** `Complexity.satStreamPos_read`, `Complexity.satDrop_move`, `Complexity.satStreamPos_succ`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
