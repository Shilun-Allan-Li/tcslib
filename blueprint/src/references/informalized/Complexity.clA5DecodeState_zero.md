<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5DecodeState_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial decoding state

**Claim.** For every binary word $w$, the decoding state at count zero is the pair encoding of $w$ with the pair encoding of two empty words.

**Proof.** At count zero, the unary word of length zero is empty. The remaining conditional field compares the natural number represented by $w$ with zero. If it is at most zero, it must equal zero, so its unary representation is empty; if it is not at most zero, the conditional field is empty by definition. In either case the final field is empty, giving the claimed nested pair encoding.
