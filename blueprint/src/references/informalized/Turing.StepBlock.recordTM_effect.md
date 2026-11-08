<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordTM_effect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of the Record Machine

**Claim.** Under the stated initial-state, record-content, encoding-prefix, tape-agreement, and summary hypotheses, after $4k+5$ steps the record machine has applied the encoded action's operational effects to the represented configuration, while halting with its output list unchanged. It has not halted earlier, the encoding is long enough, and the stated head-motion bounds hold throughout the run.

**Proof.** The execution lemma identifies the configuration after $4k+5$ steps: it is obtained by reading the full record and applying the resulting payload action, which has the encoded action's input movement, work-tape operations, and output, with its successor state set to halting (\texttt{recordTM\_execute}). The encoding-prefix hypothesis ensures that the payload is this action; the head-position agreement on the first $k$ tapes, together with the fact that these tapes are disjoint from the record tape, identifies their contents and positions with those produced by applying the original action. The summary tape is updated according to the output summary: appending the action's optional output changes the summary by precisely the rule in \texttt{outputSummary\_append}. The payload changes no output list, so the machine's output remains the initial list. The movement estimates at all intermediate times are supplied by the recording envelope lemma (\texttt{recordTM\_envelope}), and the encoded action has length at least $4k+5$ by \texttt{codeActionK\_length}.

**Key facts.** `Turing.StepBlock.recordTM_execute`, `Turing.StepBlock.mirror_ne_table`, `Turing.StepBlock.outputSummary_append`, `Turing.StepBlock.recordTM_envelope`, `Turing.codeActionK_length`.
