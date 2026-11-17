<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.linear_bool_iff_character_aux_h_eq_h -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Character Lift Is XOR-Additive

**Claim.** If a Boolean function's sign lift equals a Walsh character, then its sign at $x\oplus y$ equals the sign of the XOR of its values at $x$ and $y$.

**Proof.** A Walsh character is multiplicative under componentwise XOR, so its value at $x\oplus y$ is the product of its values at $x$ and $y$ (BoolBLR.linear_bool_iff_character_aux_h_char). Applying the hypothesis that the sign lift equals this character at the three inputs, the auxiliary equality translates that multiplicativity into equality between the sign of $f(x\oplus y)$ and the sign of $f(x)\oplus f(y)$ (BoolBLR.linear_bool_iff_character_aux_h_eq).

**Key facts.** `BoolBLR.linear_bool_iff_character_aux_h_char`, `BoolBLR.linear_bool_iff_character_aux_h_eq`.
