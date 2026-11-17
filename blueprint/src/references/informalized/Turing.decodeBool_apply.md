<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.decodeBool_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an embedded Boolean

**Claim.** For an injective map $e$ from the Boolean set into a type with decidable equality, decoding the image $e(b)$ of either Boolean $b$ returns that Boolean.

**Proof.** If $b$ is false, injectivity ensures that $e(false)$ differs from $e(true)$. Thus the first test in the decoder fails and the second succeeds, returning false. If $b$ is true, the first test succeeds immediately and returns true.
