<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.linear_bool_iff_character_aux_h_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Lifts Give XOR Compatibility

**Claim.** If the sign lift of a Boolean function equals a character and that character is multiplicative at $x,y$, then the sign of the function at $x\oplus y$ equals the sign of the XOR of its values at $x$ and $y$.

**Proof.** Evaluate the equality between the sign lift and the character at $x\oplus y$, at $x$, and at $y$. The assumed multiplicativity of the character identifies its value at $x\oplus y$ with the product of its values at $x$ and $y$. Replacing those character values by the corresponding lifted function values gives the product of the signs of $f(x)$ and $f(y)$. The sign of the Boolean XOR is exactly that product (BoolFourier.BoolToPM1_xor), proving the claimed equality.

**Key facts.** `BoolFourier.BoolToPM1_xor`.
