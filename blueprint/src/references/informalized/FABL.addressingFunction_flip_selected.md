<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingFunction_flip_selected -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping the selected data coordinate

**Claim.** Flipping the data coordinate selected by the address coordinates of $x$ changes the addressing function's value at $x$ to its negative.

**Proof.** Decompose the input into its address part and data part. Flipping the selected data coordinate preserves the address part (`FABL.addressingInputEquiv_first_flip_selected`), so the selected index remains the same. The addressing function reads the data coordinate at that index (`FABL.addressingInputEquiv_dataCoordinate`). Because this is exactly the coordinate being flipped, its sign is replaced by its negative; therefore the function's value is negated.

**Key facts.** `FABL.addressingInputEquiv_first_flip_selected`, `FABL.addressingInputEquiv_dataCoordinate`.
