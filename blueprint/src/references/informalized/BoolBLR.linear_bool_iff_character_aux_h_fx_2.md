<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.linear_bool_iff_character_aux_h_fx_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity formula from basis values

**Claim.** For every input vector, a linear Boolean function equals the parity of the number of coordinates where the input and the function’s value on that coordinate’s basis vector are both true.

**Proof.** Take the subset $s$ of coordinates on which $x$ is true. Its indicator vector agrees with $x$ at every coordinate, so applying the indicator-vector formula `linear_bool_iff_character_aux_h_fx_1` to $s$ gives the desired result. The sum over that subset is the same as the sum over coordinates filtered by the condition $x_i=1$.

**Key facts.** `BoolBLR.linear_bool_iff_character_aux_h_fx_1`.
