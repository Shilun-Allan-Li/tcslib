<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.LogProg.astep_call₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary First-Argument Oracle Call

**Claim.** When the instruction at $l$ calls oracle $j$ in unary-first mode with the single argument register $r$, on input encoding $1^n$ followed by $w$, one abstract step chooses $l_1$ exactly when the oracle accepts the pair encoding of $1^n$ and the binary word of $v(r)$, and otherwise chooses $l_0$, leaving registers and result unchanged.

**Proof.** Unfold the abstract transition at the call instruction. Its oracle query is the virtual word obtained by rendering the unary-first input segment and the single argument segment. The unary-first rendering identity (`vword_unary₁`) identifies that virtual word with the pair encoding of $1^n$ and the argument word. Taking the argument word to be the binary representation of $v(r)$ gives the stated query. The call transition selects $l_1$ or $l_0$ according to that Boolean answer and leaves the other configuration components unchanged.

**Key facts.** `Complexity.LogProg.vword_unary₁`.
