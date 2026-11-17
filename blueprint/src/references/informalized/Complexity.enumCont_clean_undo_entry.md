<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_undo_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatch into Captured Restoration

**Claim.** If $c$ is halted, one step of the clean wrapper from the captured logged configuration of $c$ with history $h$ equals the captured restoration checkpoint for $c$ and $h$, retaining $c$'s output on the capture tape and leaving physical output empty.

**Proof.** Because $c$ is halted, its state is none. The captured logged configuration consequently has the clean wrapper's administrative control for dispatch, so the wrapper takes the transition prescribed for administrative phase zero. This transition is the captured undo-entry action: it enters the undo machine at its initial state and moves the capture tape head one position to the left, while producing no physical output. The input head does not move, by the zero-movement identity (`Turing.moveInputPos_zero`). On each original tape, the undo-entry action makes no change; on the log and marker tapes it establishes the same blank or head-position data specified by the undo checkpoint. Unpacking the tape blocks shows these contents and head positions coincide with `enumCont_undoCfg c h c.inputPos`; the state and output fields also agree. Thus the resulting configuration is exactly the captured restoration checkpoint.

**Key facts.** `Turing.moveInputPos_zero`.
