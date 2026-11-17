<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.FinTM.toCodeTM_computesInTime_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time Preservation Under State Coding

**Claim.** For a one-work-tape finite-state machine, relabelling its states by the canonical finite state set with the same cardinality preserves whether it computes a given output from a given input in $t$ steps.

**Proof.** After unfolding the coding construction, the coded machine is the original machine with its states relabelled by a bijection. Relabelling commutes with running from the initial configuration: at every time, the coded configuration is the original configuration with its state mapped by that bijection (`relabelState_runFrom_init`). A bijection preserves whether the state is the halting state, and the relabelling does not change the output. The computation-time condition records halting and output at time $t$; its space-witness component can be chosen freely on either side. Therefore each machine computes the specified output at time $t$ exactly when the other does.

**Key facts.** `Turing.MultiTapeTM.relabelState_runFrom_init`.
