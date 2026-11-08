<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.tabAns_sym_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Tape Selector Answer

**Claim.** For an input-tape symbol selector, the table answer after the specified number of signed moves is the blank-symbol test applied to the input symbol at the corresponding signed offset from the current head position.

**Proof.** Unfold the table answer and the selector-answer function in the case where the selected tape is the input tape. The selector-answer function applies the blank-symbol test to the input symbol of the configuration reached after the prescribed walk. The walked-input identity identifies that symbol with the input symbol at the original configuration's signed offset (walked-input identity, `Complexity.Meyer.walked_input`). Substituting this identity gives the stated formula.

**Key facts.** `Complexity.Meyer.walked_input`.
