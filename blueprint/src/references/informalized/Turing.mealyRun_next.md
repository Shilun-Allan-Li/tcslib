<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State and Output at a Run Position

**Claim.** For any position $r$ in the input, the state after running on the first $r+1$ symbols is the state component of the transition from the state after the first $r$ symbols on input symbol $w_r$, and the output at position $r$ is that transition's output component.

**Proof.** For the state identity, write the first $r+1$ symbols as the first $r$ symbols followed by $w_r$. The run-on-concatenation law (`Turing.mealyRun_append`) says that the state after this concatenation is obtained by running the final one-symbol list from the state reached after the prefix; the definition of a one-symbol run gives the claimed transition state.

For the output identity, decompose the full input as its prefix of length $r$, then $w_r$, then the remaining suffix. Applying the same run-on-concatenation law shows that the full output is the prefix output followed by the transition output and then the suffix output. The prefix output has length $r`, by length preservation (`Turing.mealyRun_length`) and the fact that taking the first $r$ symbols gives a list of length $r$. Thus the output at index $r$ is exactly the transition output. The given bound $r<|w|$, together with length preservation, ensures that this output index exists.

**Key facts.** `Turing.mealyRun_append`, `Turing.mealyRun_length`.
