<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Scan and Parsing

**Claim.** For a natural number $f$ and a binary word $x$ with $|x|\le f$, the formula-level syntax scan accepts exactly when the fuel-bounded CNF formula parser succeeds on $x$ and leaves an empty remainder.

**Proof.** Induct on the fuel, allowing the input word to vary. At zero fuel, the length bound forces the word to be empty, and the claimed equality follows directly. With successor fuel, the empty word is immediate. If the first bit is $0$, the scanner moves to the exact-end state, so `Complexity.taut_syntax_done` says that it accepts precisely when the remaining suffix is empty; formula parsing likewise terminates with that suffix as its remainder. If the first bit is $1$, the scanner moves to clause level. The clause-scan characterization (`Complexity.taut_syntax_clause`) identifies its behavior with parsing one clause and then scanning the resulting remainder from formula level. When clause parsing fails, formula parsing fails as well. When it succeeds, `Std.Sat.CNF.parseClause_repr` expresses the input suffix as the serialization of the parsed clause followed by the remainder; the length bound therefore gives the remainder length at most the predecessor fuel. Apply the induction hypothesis to that remainder. It equates the formula-level scan with success of parsing the remaining formula and an empty final suffix, which is exactly the recursive condition in formula parsing.

**Key facts.** `Complexity.taut_syntax_cons`, `Complexity.taut_syntax_done`, `Complexity.taut_syntax_clause`, `Std.Sat.CNF.parseClause_repr`.
