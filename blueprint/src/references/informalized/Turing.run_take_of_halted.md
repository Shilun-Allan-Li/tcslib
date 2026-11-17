<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceWords.lean :: Turing.run_take_of_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run determined by its first choices

**Claim.** If every run on a word of length $t$ is halted and a halted run is unchanged by appending any word, then every word of length at least $t$ has the same run result as its prefix of length $t$, and that prefix is itself halted and has length $t$.

**Proof.** Since $t\le |w|$, the prefix $w$ take $t$ has length exactly $t$ (`List.length_take_of_le`). The hypothesis about all words of length $t$ therefore says that running on this prefix is halted. Write $w$ as its prefix of length $t$ followed by the remaining suffix, using the take-and-drop decomposition (`List.take_append_drop`). The halted-run absorption hypothesis says that appending this suffix does not change the run result. Hence the run on $w$ equals the run on its length-$t$ prefix, with the asserted length and halted property.
