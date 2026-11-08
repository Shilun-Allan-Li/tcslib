<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.xorVec_xorVec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of exclusive-or translation

**Claim.** Applying coordinatewise exclusive-or with $c$ twice to $z$ returns $z$.

**Proof.** Evaluate the two vectors at any coordinate. At that coordinate the value is $(z_i\mathbin{\mathrm{xor}}c_i)\mathbin{\mathrm{xor}}c_i$, which equals $z_i$ because exclusive-or with a fixed Boolean value is an involution. Equality at every coordinate gives equality of the vectors.
