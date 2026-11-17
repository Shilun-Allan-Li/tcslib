<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.norm_char_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit Modulus of Fourier Characters

**Claim.** Every Fourier character value has norm $1$.

**Proof.** A character value is `toOmega` applied to the dot product of its index and input. The root-of-unity map has norm $1` (`norm_toOmega`), so the character value has norm $1` as well.

**Key facts.** `ZkFourier.norm_toOmega`.
