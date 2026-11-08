<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeTable2Bits_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Table Code Length

**Claim.** For every $n$ and every table assigning a two-work-tape action to each state and each triple of optional binary symbols, its Boolean code has length at least $351(n+1)$.

**Proof.** Each action code has length at least $13$: the action-length bound gives $4k+5$ bits, which is $13$ when $k=2$ (`Turing.codeActionK_length`). Apply the flat-map length bound first to the innermost list of three choices for the second work symbol: this contributes at least $3\cdot13=39$ bits for each fixed state, input symbol, and first work symbol. Applying the same bound to the three first-work-symbol choices gives $117$ bits for each state and input symbol; applying it to the three input-symbol choices gives $351$ bits per state. Finally there are $n+1$ states, so one last application of the flat-map length bound yields at least $351(n+1)$ bits in total (`Turing.codeFlatMap_length`).

**Key facts.** `Turing.codeActionK_length`, `Turing.codeFlatMap_length`.
