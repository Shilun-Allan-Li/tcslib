<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTape_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a block coordinate

**Claim.** At position $(N+1)z+j$, the induced tape has the $j$th entry of the block assigned to $z$.

**Proof.** By definition, reading the induced tape at an integer position selects its quotient block coordinate and its remainder offset. At the position $(N+1)z+j$, these coordinates are respectively $z$ and $j$ (`arCoords`). Substituting them into the definition of the induced tape gives the stated entry.

**Key facts.** `Turing.FinTM.arCoords`.
