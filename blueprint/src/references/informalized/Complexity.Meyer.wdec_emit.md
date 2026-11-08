<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wdec_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output When the Decision Tape Is Blank

**Claim.** If the auxiliary decision tape is blank at its head position, then one step from the waiting-decision configuration halts and outputs the bit answering the decoded selector from the current simulated configuration.

**Proof.** The step formula for the constructed machine (`lcfg_step`) reduces the transition to the waiting-decision branch of its transition table. In that branch, the selector is decoded, and the auxiliary-tape read facts (`aux_read2` and `aux_read0`) identify the third auxiliary tape as blank and the first as the simulated input-symbol read; the main work-tape reads are exactly those of the simulated configuration (`mreads`). With the decision tape blank, this branch emits the selector answer and enters the halting state. The configuration-update identity (`lcfg_apply_aux`) translates that transition into the stated output and state fields; the auxiliary tape actions do not alter the simulated configuration or its scanned symbols.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read2`, `Complexity.Meyer.aux_read0`, `Complexity.Meyer.mreads`, `Complexity.Meyer.lcfg_apply_aux`.
