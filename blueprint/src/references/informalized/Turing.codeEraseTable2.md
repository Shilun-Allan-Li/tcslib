<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeEraseTable2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-tape transition table erasure

**Claim.** For every $n$ and bit string $x$, discarding the decoded transition table for $n+1$ states, with three symbol choices in each of its three symbol-indexed dimensions and two work tapes, gives exactly the result of the corresponding table skipper.

**Proof.** Begin with the vector of $n+1$ table rows. The vector erasure law (`Turing.codeEraseVec`) replaces its reader by repeated applications of the skipper for one row. A row consists of three successive symbol-indexed reads, so symbol-row erasure (`Turing.codeEraseSymbols`) replaces each such reader by three repetitions of the skipper for its entry. Each entry is a two-work-tape action, and action erasure (`Turing.codeEraseActionK`) replaces that reader by the corresponding action skipper. Substituting these equalities yields the nested repetitions in the stated table skipper, with the same success or failure and final suffix.

**Key facts.** `Turing.codeEraseVec`, `Turing.codeEraseSymbols`, `Turing.codeEraseActionK`.
