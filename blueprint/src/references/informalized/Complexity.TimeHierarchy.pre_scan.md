<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.pre_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preprocessing Scan Bound

**Claim.** Starting in state $\mathrm{scan0}$ at the beginning of the suffix $r$, the machine reaches $\mathrm{rwStart}$ within $|r|+1$ steps and has emitted exactly the prefix $\mathrm{scanPre}(r)$ after its prior output.

**Proof.** Induct on the shape of the remaining suffix. If it is empty, the head reads the end marker and the scan transition goes directly to $\mathrm{rwStart}$ in one step, emitting nothing. If it is a singleton $[b]$, the machine first emits $b$ and moves right into the state remembering $b$; at the end marker its next step enters $\mathrm{rwStart}$. Thus it takes two steps and emits $b$, as required. For a suffix $b::b'::s$, the first two steps emit $b,b'$ and move the machine to the position before $s$. If $b=b'$, the machine returns to $\mathrm{scan0}$, so apply the induction hypothesis to $s$ and concatenate those two initial steps with the resulting run. The run-composition identity (`runFrom_add`) gives the combined time bound, and the definition of $\mathrm{scanPre}$ gives the stated output. If $b\ne b'$, the second step already enters $\mathrm{rwStart}$, and the output is exactly the retained pair. In each case, `inputSymbol_at` identifies the symbols read from the head position, `moveInputPos_pos_of_ne_right` gives the rightward head updates, and the one-step transition equation (`preTM_step`) supplies the machine’s state and output changes.

**Key facts.** `Complexity.TimeHierarchy.preTM_step`, `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_add`.
