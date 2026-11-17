<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_parse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact CNF Parsing

**Claim.** For every finite binary string $x$, the syntax scanner started in the formula state ends in the exact-end state exactly when the exact-consumption parser returns a CNF formula on $x$.

**Proof.** Apply the formula-state scan characterization at fuel $|x|$. It identifies the scanner’s result with whether parsing the clauses using that fuel succeeds and leaves an empty remainder. Unfolding the exact-consumption parser, if clause parsing fails then both sides are false; if it returns a formula and remainder, both sides are true precisely when that remainder is empty.

**Key facts.** `Complexity.taut_syntax_formula`.
