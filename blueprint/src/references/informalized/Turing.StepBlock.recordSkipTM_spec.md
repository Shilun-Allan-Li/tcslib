<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordSkipTM_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recording-Machine Run Specification

**Claim.** For every time up to the encoding length plus one, the recording-and-skip machine preserves input position, tape contents, and output and has the stated head positions; before that terminal time it is not in a tagged done state.

**Proof.** The serialization-reading lemma decomposes the action bits into the fixed-width record and its successor-state field, gives the total length, and transfers the assumed tape contents to the two segments (`Turing.StepBlock.actionBitsK_reads`). Apply the path result to this decomposition (`Turing.StepBlock.recordSkipTM_path`). Its state assertion excludes tagged done states for every time strictly before the full encoding length plus one. Its configuration assertions give the unchanged input position, tape contents, and output, together with the stated table-tape displacement and zero displacement on every other work tape. These are exactly the two conclusions.

**Key facts.** `Turing.StepBlock.actionBitsK_reads`, `Turing.StepBlock.recordSkipTM_path`.
