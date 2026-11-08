<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_position_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Input Position Update

**Claim.** The record machine can update its buffered binary representation of the simulated input-head position to match one action of the simulated machine, reaching the skip-new-position stage within the stated time and head-displacement bounds while avoiding both verdict states.

**Proof.** Let $W$ be the bit width and let $w$ and $v$ be the fixed-width binary words for the old and new input-head positions. The position-digit calculation ( `recordStep_position_digits` ) says that a zero movement, a left movement at the left boundary, or a right movement past the right boundary leaves the represented position unchanged; in the remaining left and right cases, decrementing or incrementing the fixed-width word gives exactly $v$.

If the word is unchanged, the machine clears the temporary copy on tape 1. The clear-snapshot result ( `recordStep_clear_snapshot` ) gives this pass's endpoint and head bounds, and the phase-transition result ( `recordStep_phase_run` ) incorporates that pass into the record machine's control flow, ending at skip-new-position. Since the represented word did not change, the target snapshot's updated tape 0 agrees with the original tape 0 on the specified interval and the rest of the configuration is unchanged.

In the increment and decrement cases, the fixed-width arithmetic transport result ( `recordStep_arithmetic_transport` ) runs the corresponding binary operation on the temporary bank within its stated time and head bounds. The phase-transition result carries the run to the copy-back stage, and the copy-back result ( `recordStep_copyback_run` ) transfers the resulting word to tape 0 and reaches skip-new-position. Composing the two runs uses the concatenation principle for record runs ( `recordRun_trans` ); the supplied length equalities and arithmetic bound give the claimed total time. In each branch, the phase-run bounds exclude both verdict states before the endpoint and keep every work head within radius $W+1$.

**Key facts.** `Turing.recordStep_position_digits`, `Turing.recordStep_clear_snapshot`, `Turing.recordStep_phase_run`, `Turing.recordStep_arithmetic_transport`, `Turing.recordStep_copyback_run`, `Turing.recordRun_trans`.
