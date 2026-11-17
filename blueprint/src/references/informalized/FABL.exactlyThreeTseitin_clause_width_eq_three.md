<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.exactlyThreeTseitin_clause_width_eq_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width after Tseitin conversion

**Claim.** If a CNF formula has width at most $w$ with $w\geq 3$, then every clause in its three-literal Tseitin conversion has width exactly three.

**Proof.** The three-literal Tseitin conversion first produces a formula of width at most three from the original formula, using the hypotheses that its width is at most $w$ and that $w\geq3$ (`FABL.widthThreeTseitin_width_le`). The exactly-three conversion preserves that width bound while ensuring every resulting clause has width exactly three (`FABL.exactlyThreeCNF_clause_width_eq_three`). Applying this result to the intermediate formula and the given clause proves the assertion.

**Key facts.** `FABL.widthThreeTseitin_width_le`, `FABL.exactlyThreeCNF_clause_width_eq_three`.
