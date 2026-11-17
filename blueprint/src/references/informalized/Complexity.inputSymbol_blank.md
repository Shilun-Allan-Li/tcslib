<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.inputSymbol_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Input Reads Occur at the Boundaries

**Claim.** A configuration’s input-head read is absent exactly when its position is $0$ or $|x|+1$.

**Proof.** By the definition of the input read, position $0$ gives no symbol, and position $|x|+1$ also gives no symbol. At every other position, the head reads the list entry at index one less than its position. The configuration’s position lies in the range from $0$ through $|x|+1$, so that index is valid and the entry is present. Thus absence occurs exactly at the two boundary positions.
