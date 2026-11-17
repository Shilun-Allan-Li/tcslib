<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingFunction_flip_data_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Irrelevant data-coordinate flip

**Claim.** If a data index $j$ differs from the index encoded by the address coordinates of $x$, flipping data coordinate $j$ leaves the addressing function's value at $x$ unchanged.

**Proof.** Decompose the input into its address part and data part. Flipping data coordinate $j$ leaves the address part fixed (`FABL.addressingInputEquiv_first_flip_data`), so the address still selects the same data index. The selected data value is the coordinate of the input at that selected data position (`FABL.addressingInputEquiv_dataCoordinate`). Since the selected index differs from $j$, the coordinate flip does not change that selected coordinate (`FABL.setCoordinate_apply_of_ne`). Hence the addressing function has the same value before and after the flip.

**Key facts.** `FABL.addressingInputEquiv_first_flip_data`, `FABL.addressingInputEquiv_dataCoordinate`, `FABL.setCoordinate_apply_of_ne`.
