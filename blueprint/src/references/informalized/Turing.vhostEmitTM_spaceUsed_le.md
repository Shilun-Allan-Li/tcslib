<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Virtual Simulation Space Bound

**Claim.** The virtual simulation uses at most the space used by $M$ through step $t$, plus $|y|+2$.

**Proof.** The buffer tape head of the virtual simulation visits only positions in the integer interval $[-1,|y|]$: this follows by applying the buffer-head containment result (`Turing.vhostCfg_buffer_head_mem`) to each time in the visited-position set. That interval has $|y|+2$ integers, so the buffer tape uses at most that many cells. For each bank tape $i$, the visited-head theorem (`Turing.vhostEmitTM_visitedByTapeHead_bank`) identifies its visited positions exactly with those on work tape $i$ of $M$, hence their space counts agree. The bank tapes are precisely all tapes except the buffer tape, so summing their counts gives $M$'s total space; adding the buffer contribution and using its bound proves the claim.

**Key facts.** `Turing.vhostCfg_buffer_head_mem`, `Turing.vhostEmitTM_visitedByTapeHead_bank`.
