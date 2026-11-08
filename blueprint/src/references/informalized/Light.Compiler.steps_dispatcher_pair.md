<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.steps_dispatcher_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Dispatcher Comparison Step

**Claim.** If the dispatcher for $n$ procedures begins at $\mathrm{disp}$, $j<n$, the one-register encodes $1$, and $v-1$ is in signed range, then from position $\mathrm{disp}+2j$ with return-register value $v$, two steps leave that register encoding $v-1$ and move to $j$ when $v-1<0$, or to $\mathrm{disp}+2(j+1)$ otherwise.

**Proof.** The relevant dispatcher pair at offset $j$ consists of a subtraction followed by a conditional branch (`codeAt_dispatcher`). The subtraction computes $v-1$ in the return register, using the one-register value $1$ (`steps_sub`). The signed-range hypothesis ensures the branch interprets this word with the intended sign. The branch therefore goes to $j$ if $v-1<0$, and otherwise advances past the pair to $\mathrm{disp}+2(j+1)$ (`steps_bltz`). Combining the two one-step runs gives the stated two-step behavior (`Steps.trans`).

**Key facts.** `Light.Compiler.codeAt_dispatcher`, `WordRAM.steps_sub`, `WordRAM.steps_bltz`, `WordRAM.Steps.trans`.
