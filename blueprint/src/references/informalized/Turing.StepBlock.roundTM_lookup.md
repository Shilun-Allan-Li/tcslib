<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_lookup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup Within One Round

**Claim.** The lookup phase selects the transition-table entry for the state and scanned symbols of the configuration. It identifies the serialized action as a contiguous block, with the state index no farther into the table than the preceding block, and reaches the state-tail configuration within the stated time bound while satisfying the round-span conditions.

**Proof.** Start the lookup phase with the transition table on the table tape, the output summary and unary state encoding on the summary tape, and both auxiliary heads at zero. The selection result `seekTM_select` finds the block of the table corresponding to the observed input and work-tape symbols and the unary state. It supplies a prefix `before`, a suffix `tail`, and a time $T$ such that the table is `before` followed by the selected action's encoding followed by `tail`; it also establishes $q\le |\mathrm{before}|$ and the lookup-time bound. This is the search through the serialized table: the summary tape guides the scan, and the table head's position records the prefix length.

The selector's endpoint is transferred into the full round machine using `roundTM_phase`. Its hypotheses ensure that no earlier control state triggers a redirection, that the endpoint redirects to the state-tail phase, and that the input head and original work heads stay within the round window. The auxiliary heads are then shifted to the positions specified by the prefix and unary state encoding: `roundData_shift` identifies this shifted configuration with the stated `roundData`, while `roundWindow_frame` preserves the window property across the phase-control transition. This redirection adds one step, so the total time is $T+1$; the selector's bound yields the claimed bound in terms of the table length.

**Key facts.** `Turing.StepBlock.seekTM_select`, `Turing.StepBlock.roundTM_phase`, `Turing.StepBlock.roundData_shift`, `Turing.StepBlock.roundData_window`, `Turing.StepBlock.roundWindow_frame`.
