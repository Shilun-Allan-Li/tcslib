<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.linear_bool_iff_character_aux_h_fx_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity on indicator vectors

**Claim.** For every subset of coordinates, the value of a linear Boolean function on its indicator vector is the parity of the number of coordinates in the subset where the function is true on the corresponding basis vector.

**Proof.** Fix a subset $s$ and induct on its elements. For the empty subset, its indicator vector is the zero vector. Linearity applied to the zero vector XOR itself shows that the function takes the value false there, matching the empty sum, which is even. For the inductive step, write the subset as a new element $i$ together with a subset not containing $i$. Its indicator vector is the XOR of the basis vector $e_i$ and the indicator vector of the smaller subset. By linearity, the function’s value is the XOR of its values on those two vectors. The corresponding count of successful basis coordinates is the smaller count plus one exactly when $f(e_i)$ is true; hence its parity changes exactly in that case. This gives the claimed formula for the enlarged subset.
