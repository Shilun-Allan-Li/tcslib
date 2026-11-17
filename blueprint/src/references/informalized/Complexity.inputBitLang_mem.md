<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.inputBitLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Bit Language in Logarithmic Space

**Claim.** The language of encoded pairs whose indicated bit of the first string is $1$ is decidable in logarithmic space, with a constant-factor bound in the input length.

**Proof.** The identity function on encoded strings is implicitly logarithmic-space computable (`implicitlyLogspaceComputable_id`). Its first component gives the input-bit language, so the claimed membership in logarithmic space follows directly from that result.

**Key facts.** `Complexity.implicitlyLogspaceComputable_id`.
