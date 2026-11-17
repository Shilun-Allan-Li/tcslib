<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamPos_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at a clamped offset

**Claim.** If the input-head position of a configuration is the clamped position corresponding to $i$, then the symbol read is the optional entry $x[i]?$.

**Proof.** Apply the input-symbol-at-position fact at the valid input offset $\min(i,|x|)$. The clamped-position hypothesis identifies the head's numerical position with this offset plus one, as required by that fact. If $i\leq |x|$, the minimum is $i$, so the read symbol is $x[i]?$. If $i>|x|$, the minimum is $|x|$; the head reads at the end of the input, and both the read symbol and the out-of-range optional list entry are none.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
