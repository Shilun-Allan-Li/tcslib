<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Scan and Parsing

**Claim.** For a fuel bound $f$ and a binary word $x$ with $|x|\le f$, the clause-level syntax scan accepts exactly when parsing one clause from $x$ with fuel $f$ succeeds and the scanner accepts the resulting remainder from formula level; if parsing fails, the scan rejects.

**Proof.** Induct on the fuel, allowing the word to vary. With zero fuel, the length bound forces the word to be empty, and both sides reject. For successor fuel, the empty word and a word beginning with $0$ are immediate: the latter ends the clause, leaving its suffix for formula-level scanning. If the word begins with $1$, the scanner first processes a literal. The literal-scan characterization (`Complexity.taut_syntax_literal`) says this succeeds precisely when literal parsing succeeds, after which scanning continues at clause level on the literal parser's remainder. If literal parsing fails, both the scan and clause parser reject. If it succeeds, `Std.Sat.CNF.parseLit_repr` expresses the original word as the serialization of that literal followed by the remainder; comparing lengths with the fuel bound shows that the remainder has length at most the predecessor fuel. Now split according to whether parsing the remaining clause succeeds. On failure, the clause-level scan and parser both fail. On success, apply the induction hypothesis to that remainder: its scan agrees with whether parsing the remaining clauses succeeds and leaves a suffix accepted from formula level. This is exactly the recursive clause-parsing condition, completing the comparison.

**Key facts.** `Complexity.taut_syntax_literal`, `Std.Sat.CNF.parseLit_repr`.
