<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_shiftRight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Scan Transformation

**Claim.** The rightward scan returns the last get-value, or b₀ for the empty word, and pairs each symbol with the corresponding entry of b₀ followed by the get-values of the word.

**Proof.** The second keep scan reduces the two-pass result to the first pass (`Turing.scanResult_keep`). Induct on the word, generalizing the initial state b₀ because the induction step uses the current state as the seed for the tail. For the empty word, the state remains b₀ and the output is empty. For γ :: w, the first transition changes the state to get γ and the head to set γ b₀. The induction hypothesis on w, now starting from get γ, returns the last get-value of w (or get γ when w is empty) and pairs the tail with get γ followed by the get-values of w. Prepending the changed head gives exactly the zip of γ :: w with b₀ followed by the get-values of γ :: w; the state is the last get-value of the whole word, with the stipulated empty-word fallback.

**Key facts.** `Turing.scanResult_keep`.
