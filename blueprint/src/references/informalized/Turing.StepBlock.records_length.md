<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.records_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Length of a List of Actions

**Claim.** For every finite list of actions, its number of actions is at most the length of the concatenation of their binary encodings.

**Proof.** Induct on the list. The empty list has both lengths zero. For a list with first action $a$ and tail $as$, the concatenated encoding has length equal to the length of the encoding of $a$ plus the length of the tail's concatenated encoding. Each individual action encoding has length at least $4k+5$, in particular at least one (\texttt{codeActionK\_length}); combining this with the induction hypothesis gives the desired inequality.

**Key facts.** `Turing.codeActionK_length`.
