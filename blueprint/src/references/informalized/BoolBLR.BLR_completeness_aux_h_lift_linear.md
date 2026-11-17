<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.BLR_completeness_aux_h_lift_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Sign Lift Preserves XOR Addition

**Claim.** If a Boolean function respects componentwise XOR, then its \{-1,1\} lift sends XOR of inputs to multiplication of signs.

**Proof.** Fix $x,y$. The hypothesis identifies $f(x\oplus y)$ with the Boolean XOR of $f(x)$ and $f(y)$. The sign of a Boolean XOR is the product of the two signs (BoolFourier.BoolToPM1_xor). Applying this identity to the output values gives $g(x\oplus y)=g(x)g(y)$.

**Key facts.** `BoolFourier.BoolToPM1_xor`.
