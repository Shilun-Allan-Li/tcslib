<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.ampAs_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification Languages in Logarithmic Space

**Claim.** Each of the four languages in the family associated with $N$ belongs to logarithmic space.

**Proof.** A case split on the index $j\in\{0,1,2,3\}$ identifies the corresponding language in the family. For $j=0$ it is the input-length language, which belongs to logarithmic space (`inputLenLang_mem`). For $j=1,2,3$ the languages are respectively the initialization, one-step, and acceptance configuration-code languages; each belongs to logarithmic space by its corresponding result (`Codec.initLang_mem`, `Codec.stepLang_mem`, and `Codec.acceptLang_mem`). These four cases establish the claim for every index.

**Key facts.** `Complexity.inputLenLang_mem`, `Complexity.Codec.initLang_mem`, `Complexity.Codec.stepLang_mem`, `Complexity.Codec.acceptLang_mem`.
