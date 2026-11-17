<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.seekTM_request -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Processing One Search Request

**Claim.** From a request state with rank, remaining count, and flag as specified, and with one action's encoding present at the table head, the search machine processes that encoding in its length plus three steps. It reaches the control state prescribed by the request successor, advances the table head by the encoding length, does not reach done earlier, and preserves the input position, tape contents, output, and all other work-tape heads throughout.

**Proof.** The first transition leaves the request state and enters the record-skipping phase, without moving the input head. This is the input-move action step (`Turing.step_of_inputMoveAction`). The record-skipping machine then scans the action encoding and finishes after its encoding length plus one steps. Its endpoint is supplied by `recordSkipTM_run`: the table head has advanced by exactly the encoding length, and the phase records whether the decoded action has a successor state. Its specification (`recordSkipTM_spec`) ensures the phase does not reach its terminal done state earlier and that the input position, tapes, output, and other heads are preserved. The phase-hosting principle (`Turing.phaseHostTM_run`) identifies this hosted run with the record-skipping run at each intermediate time, then performs the phase reduction at its endpoint. That reduction returns the search machine to its router with control `seekNext rank rest last`. Including the initial transition yields the stated total of encoding length plus three. The intermediate-state specification rules out reaching the search machine's done control before the endpoint, and its frame property transfers the preservation claims to the full run.

**Key facts.** `Turing.step_of_inputMoveAction`, `Turing.StepBlock.recordSkipTM_run`, `Turing.StepBlock.recordSkipTM_spec`, `Turing.phaseHostTM_run`.
