<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.inputSymbol_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol by head position

**Claim.** For any configuration on Boolean input $x$, the symbol under its input head is `none` at position zero and otherwise is the optional symbol of $x$ at index one less than the head position.

**Proof.** If the head position is zero, its value identifies the zero position, and the definition of the input symbol gives `none`. Otherwise, the head is at a positive position. Rewriting that position as one plus the index immediately to its left, the input-symbol-at-position fact ($\texttt{Turing.FinTM.inputSymbol\_at}$) identifies the scanned symbol with the optional list entry at that index.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
