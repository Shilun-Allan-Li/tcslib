<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.inputLenLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Length Language in Logarithmic Space

**Claim.** The language of encoded pairs for which the index is less than the length of the first string is decidable in logarithmic space, up to a constant factor.

**Proof.** The identity function is implicitly logarithmic-space computable (`implicitlyLogspaceComputable_id`). The second component of this result gives membership of the input-length language in logarithmic space, yielding the claim.

**Key facts.** `Complexity.implicitlyLogspaceComputable_id`.
