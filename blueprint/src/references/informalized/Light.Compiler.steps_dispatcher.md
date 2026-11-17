<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.steps_dispatcher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher Selects a Procedure

**Claim.** If the dispatcher for $n$ procedures begins at position $\mathrm{disp}$, $r<n$, $2n<2^W$, the one-register encodes $1$, and the return-register encodes $r$, then after $2(r+1)$ steps the program counter is $r$ and the return-register encodes $-1$.

**Proof.** Apply the dispatcher progress result from offset $j=0$ with counter value $k=r$. Its condition $j+k<n$ is exactly $r<n$, and it gives a run of $2(r+1)$ steps from position $\mathrm{disp}$ with the return-register encoding $r$ to position $0+r=r$, leaving that register encoding $-1$ (`steps_dispatcher_from`). The assumed initial register value identifies the memory update in that result with the original memory, so its initial configuration is the one claimed.

**Key facts.** `Light.Compiler.steps_dispatcher_from`.
