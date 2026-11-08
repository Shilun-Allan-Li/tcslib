<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parse_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Parses Back to Its Formula

**Claim.** For every CNF formula $\varphi$, exact-consumption parsing of its binary encoding returns $\varphi$.

**Proof.** The serialization-parsing theorem for clause sequences says that, whenever the fuel is at least the length of the serialized formula, parsing that encoding followed by any remainder returns the formula and that remainder (\texttt{parseClauses\_serialize}). Apply it with empty remainder and fuel equal to the encoding's length; the length bound is then immediate. The parser therefore returns $(\varphi,[])$. Exact-consumption parsing accepts precisely this result, so it returns $\varphi$.

**Key facts.** `Std.Sat.CNF.parseClauses_serialize`.
