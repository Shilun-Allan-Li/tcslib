<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.steps_dispatcher_from -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher Progress From an Offset

**Claim.** If the dispatcher for $n$ procedures begins at position $\mathrm{disp}$, $2n<2^W$, the one-register encodes $1$, and $j+k<n$, then from position $\mathrm{disp}+2j$ with return-register value $k$, the machine reaches position $j+k$ after $2(k+1)$ steps and leaves the return-register encoding $-1$.

**Proof.** Induct on $k$, keeping the offset $j$ general. When $k=0$, one dispatcher comparison subtracts $1$ from the return register, producing $-1$; the following conditional branch goes directly to position $j$. This is the two-instruction dispatcher pair (`steps_dispatcher_pair`). For the successor case, the pair at offset $j$ subtracts $1$ from $k+1$, leaving $k$. Since this value is nonnegative, the branch advances to the next pair at offset $j+1$. The induction hypothesis then handles the remaining $k$ comparisons from that position, reaching $(j+1)+k=j+(k+1)$ and leaving $-1$. Concatenating the two-step pair with the inductive run gives $2+2(k+1)=2((k+1)+1)$ steps; elementary arithmetic identifies the resulting position and count with the desired ones.

**Key facts.** `Light.Compiler.steps_dispatcher_pair`, `WordRAM.Steps.trans`.
