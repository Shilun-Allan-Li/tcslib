<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.tableBitsK_groups -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Grouping the transition table by state

**Claim.** The bit string encoding the transition table is the concatenation, in state order, of the action encodings for each state, with that state's entries ordered by input read and then by work-tape read tuple.

**Proof.** For each state, `readActions` concatenates the actions obtained from the work-tape reads for input `blank`, then those for input `0`, then those for input `1`. Applying `flatMap actionBitsK` to this statewise list therefore concatenates exactly the action encodings indexed by those same input and work-tape reads. Flattening the resulting lists over the states gives the defining order of `tableBitsK`; associativity of list flattening and distribution of `flatMap` over concatenation identify the two expressions.
