<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.As_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace membership of the encoded languages

**Claim.** For a finite-state nondeterministic Turing machine with Boolean input, each of the five associated languages belongs to logarithmic space: the input-bit and input-length languages, and the preimages under `dropIdx` of the initial-configuration, accepting-configuration, and single-step languages.

**Proof.** Split into the five possible values of the index. For the first two, the input-bit language and input-length language are already known to be in logarithmic space (`inputBitLang_mem` and `inputLenLang_mem`). For each of the remaining three, the corresponding configuration language—initial, accepting, or single-step—is in logarithmic space (`Codec.initLang_mem`, `Codec.acceptLang_mem`, and `Codec.stepLang_mem`). The map `dropIdx` is implicitly logspace computable (`implicitlyLogspaceComputable_dropIdx`), and the preimage theorem says that taking the preimage of a logspace language under such a map preserves logarithmic-space membership (`mem_LOGSPACE_preimage`). Applying it to each of those three languages gives the required membership for the remaining cases.

**Key facts.** `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`, `Complexity.implicitlyLogspaceComputable_dropIdx`, `Complexity.Codec.initLang_mem`, `Complexity.mem_LOGSPACE_preimage`, `Complexity.Codec.acceptLang_mem`, `Complexity.mem_LOGSPACE_preimage`, `Complexity.Codec.stepLang_mem`, `Complexity.mem_LOGSPACE_preimage`.
