<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.synOK_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Syntax Acceptance and CNF Parsing

**Claim.** For every bit string $x$, the syntax automaton accepts $x$ exactly when aligned-pair parsing succeeds and the returned second component parses completely as a CNF formula.

**Proof.** Induct on the recursive behavior of aligned-pair decoding. When the input begins with two equal bits, decoding recursively processes the remaining suffix and restores that bit to the first component. The induction hypothesis identifies the syntax-check result on the suffix; the corresponding combined syntax transition simply consumes the equal pair and resumes in the same syntax phase. Thus the equivalence is preserved in both equal-bit cases. When decoding encounters the separator $01$, the first component is complete and the automaton enters the six-state CNF syntax scanner on the remaining component. The identity between the combined scan and the six-state scan (`synStep_matrix`) reduces acceptance to acceptance by that scanner; the CNF syntax specification identifies this with successful CNF parsing (`Std.Sat.CNF.syntaxOK_spec`). Finally, if no decoding clause applies, the first unmatched bit pattern cannot be a valid separator or equal-bit pair. The automaton therefore cannot accept: in the only remaining case that requires an argument, a suffix-state characterization (`Std.Sat.CNF.syntaxSuffix_run`) rules out ending in the accepting state. These cases establish the claimed equivalence.

**Key facts.** `Complexity.LogProg.TQBFARM.synStep_matrix`, `Std.Sat.CNF.syntaxOK_spec`, `Std.Sat.CNF.syntaxSuffix_run`.
