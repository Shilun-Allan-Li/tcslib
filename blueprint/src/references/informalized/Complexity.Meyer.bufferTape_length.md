<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.bufferTape_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The first blank cell

**Claim.** For every Boolean word $w$, the tape storing $w$ starting at cell zero is blank at cell $|w|$.

**Proof.** At the natural-number cell $|w|$, the tape value is the optional list lookup $w[|w|]?$, by the natural-cell description of the tape (`bufferTape_nat`). This lookup is absent because the index equals the length of the list, so the tape value is `none`.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
