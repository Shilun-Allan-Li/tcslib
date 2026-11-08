<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeEraseActionK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action record erasure

**Claim.** For any $k,n$ and bit string $x$, the action reader and action skipper leave the same suffix whenever they succeed, so discarding the parsed action from the reader gives exactly the skipper’s result.

**Proof.** First apply the vector erasure law to the $k$ work-tape entries. Each entry is read by the work-record reader, whose erased output is exactly the work-record skipper; thus the vector reader leaves the same suffix as repeating that skipper $k$ times. This uses the vector erasure law (`Turing.codeEraseVec`) together with work-record erasure (`Turing.codeEraseWork`). Now process the action fields in order: the input movement, the work-tape vector, the output, and the successor state. Erasing each field replaces its reader by its corresponding skipper: movement by the two-bit pair skipper (`Turing.codeEraseSign`), output by the same pair skipper (`Turing.codeEraseOutput`), and the final state by the state skipper (`Turing.codeEraseState`). At each stage, the bind erasure identity (`Turing.codeErase_bind`) allows the suffix computation to be moved from the reader’s result to the reader after its value has been discarded. Chaining these equalities gives precisely the action skipper’s result, including failure in any field.

**Key facts.** `Turing.codeEraseVec`, `Turing.codeEraseWork`, `Turing.codeEraseSign`, `Turing.codeErase_bind`, `Turing.codeEraseOutput`, `Turing.codeEraseState`.
