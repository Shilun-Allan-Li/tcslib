<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.linear_bool_iff_character_aux_h_fx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity formula for linear Boolean functions

**Claim.** For every input vector, the value of a linear Boolean function is the parity of the coordinates where the input and the function’s value on the corresponding basis vector are both true.

**Proof.** The result is exactly the general input-vector parity formula established by `linear_bool_iff_character_aux_h_fx_2`. Applying that fact to $f$, its linearity hypothesis, and the given vector $x$ yields the stated equality: the function is false when the indicated count is even and true when it is odd.

**Key facts.** `BoolBLR.linear_bool_iff_character_aux_h_fx_2`.
