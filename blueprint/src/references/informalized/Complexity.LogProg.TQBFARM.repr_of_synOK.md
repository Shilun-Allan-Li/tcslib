<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.repr_of_synOK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepted Syntax Has a CNF Representation

**Claim.** If the syntax automaton accepts a bit string $x$, then there are bit strings $q$ and a CNF formula $\varphi$ over natural-number-indexed variables such that $x=\langle q,\mathrm{enc}(\varphi)\rangle$, with the specified self-delimiting pairing and binary serialization.

**Proof.** The characterization of acceptance says that an accepted string must successfully decode as a pair, and that the second component must parse as a CNF formula (\texttt{Complexity.LogProg.TQBFARM.synOK_spec}). Decode $x$. If decoding fails, the characterization forces the acceptance hypothesis to be false, so this case cannot occur. Thus $x$ decodes as $(q,y)$. Parse $y$ as a CNF formula. If parsing fails, the same characterization again contradicts acceptance. Therefore $y$ parses as some formula $\varphi$. A decoded pair reconstructs its original encoded string, so $x=\langle q,y\rangle$ (\texttt{Turing.eq_pairEncode_of_pairDecode}). The parsing representation theorem gives $y=\mathrm{enc}(\varphi)$ (\texttt{Std.Sat.CNF.parse_repr}); substituting this identity yields the required representation.

**Key facts.** `Complexity.LogProg.TQBFARM.synOK_spec`, `Turing.eq_pairEncode_of_pairDecode`, `Std.Sat.CNF.parse_repr`.
