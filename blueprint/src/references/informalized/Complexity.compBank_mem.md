<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compBank_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace membership of the query bank

**Claim.** Under the stated polynomial output-length bound and logspace decidability assumptions for the indexed output-bit and output-length languages, each of the four languages in the query bank belongs to logspace.

**Proof.** Fix an index in the four-element bank. It is one of $0,1,2,3$. At indices $0$ and $1$, the bank contains the input-bit and input-length query languages, which belong to logspace by `inputBitLang_mem` and `inputLenLang_mem`. At index $2$ or $3$, it contains the lifted output query in bit mode or length mode, respectively; both belong to logspace by `compLift_mem` under the given hypotheses. These cases cover every bank index.

**Key facts.** `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`, `Complexity.compLift_mem`.
