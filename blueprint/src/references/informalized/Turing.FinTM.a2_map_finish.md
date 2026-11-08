<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completing the input-copying phase

**Claim.** From the copy state, the simulator copies the remaining suffix $b$ into the second buffer, returns the heads to the required positions, emits the encoding of $(a,\epsilon)$, and reaches the run state representing $M$ initialized on $b$, at the right boundary of the input.

**Proof.** Split the stated number of steps into four consecutive phases: copying the remaining input suffix, returning the second-buffer head, returning the first-buffer head, and emitting the encoding. The suffix-copying result (`a2_map_suffix`) takes $|b|+1$ steps and leaves the simulator in the backB state at the right boundary, with second buffer $b$ and its head at the final position. The backB result (`a2_map_backB`), applied with $j=|b|$, takes $|b|+1$ further steps and places that head at zero while entering backA. The backA result (`a2_map_backA`), with $j=|a|$, takes $|a|+1$ steps and places the first-buffer head at zero while entering emitA. Finally, the emission result (`a2_map_emit`) with the whole first buffer as its suffix takes $2|a|+2$ steps, emits each bit of $a$ twice followed by $0,1$, and enters the run state with tag true and first-buffer head at $|a|$. The run-composition law (`runFrom_add`) joins these phases. Their lengths sum to $3|a|+2|b|+5$. The resulting configuration agrees with the claimed virtual initialization: the simulated machine is initialized on $b$, and the emitted word is exactly `pairEncode a []`.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.a2_map_suffix`, `Turing.FinTM.a2_map_backB`, `Turing.FinTM.a2_map_backA`, `Turing.FinTM.a2_map_emit`.
