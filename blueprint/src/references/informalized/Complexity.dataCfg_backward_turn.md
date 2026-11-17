<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_backward_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Turn at the Backward Boundary

**Claim.** If the guide tape is the fixed guide of radius $R$, one step from the backward phase at position $-R-1$ enters the return-center phase at position $-R$, preserving the base configuration, $u$, data register, data tapes, and output.

**Proof.** Apply the decorated-machine one-step formula (`dataCfg_step`) and the schedule transition for the backward phase (`macroCfg_backward`). At the left boundary, the backward transition takes its turning branch, so the phase becomes return-center and the guide position changes from $g$ to $g+1$. With $g=-R-1$, this is $-R$. The guide tape indeed marks that position as its left edge (`guideTape_left`), and the guide-head reading in the macro configuration is the corresponding base-tape symbol (`macroCfg_guide`). At this boundary the visitor leaves the data register and data tapes unchanged and emits no output. Therefore the decorated step has exactly the claimed fields.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.macroCfg_backward`, `Complexity.guideTape_left`, `Complexity.macroCfg_guide`.
