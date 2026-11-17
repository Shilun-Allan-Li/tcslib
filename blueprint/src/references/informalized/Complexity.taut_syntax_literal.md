<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Scan and Literal Parsing

**Claim.** For every finite binary word $x$, the clause-level scanner accepts $1$ prefixed to $x$ exactly when parsing that prefixed word as a literal succeeds and the scanner accepts the parser's remaining suffix from clause level; if parsing fails, the scan rejects.

**Proof.** The first bit $1$ takes the scanner from clause level to unary level, by the one-step scanner identity (`Complexity.taut_syntax_cons`). The unary-scan characterization (`Complexity.taut_syntax_unary`) says that scanning then consumes the run of $1$s and succeeds only when it encounters the required $0$ and following polarity bit, continuing at clause level on the suffix after them. Unfold literal parsing, which counts that initial run of $1$s and requires precisely this delimiter and polarity bit. To compare the two descriptions, write the run-counting operation's result as a length and a remainder, then split on whether that remainder has the required delimiter and polarity form. In each case, the scanner and literal parser either both fail or both return the same suffix, proving the claim.

**Key facts.** `Complexity.taut_syntax_cons`, `Complexity.taut_syntax_unary`.
