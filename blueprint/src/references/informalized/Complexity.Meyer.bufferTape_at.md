<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.bufferTape_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape contents at an occupied cell

**Claim.** For a Boolean word $w$ and a natural number $i<|w|$, the tape storing $w$ starting at cell zero contains $w_i$ at cell $i$.

**Proof.** At a natural-number cell $i$, the stored tape agrees with the list lookup $w[i]?$. Since $i<|w|$, this optional lookup is precisely the present symbol $w_i$, so the tape value is `some w[i]`. The natural-cell description of the tape is supplied by `bufferTape_nat`; the conversion from an in-bounds optional lookup to the symbol itself is the standard list lookup fact.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
