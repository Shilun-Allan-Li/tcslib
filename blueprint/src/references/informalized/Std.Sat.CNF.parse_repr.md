<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parse_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing Recovers the Encoding

**Claim.** If exact-consumption parsing of a finite bit string $x$ returns a CNF formula $\varphi$, then $x$ is exactly the specified binary encoding of $\varphi$.

**Proof.** Unfold exact-consumption parsing. Its successful case says that parsing the clauses produces some formula $\psi$ and leaves the empty remainder, and that the returned formula is $\varphi$. Thus $\psi=\varphi$. The reconstruction theorem for clause parsing says that the input is the encoding of the parsed formula followed by its remainder (\texttt{parseClauses\_repr}). With the remainder empty, this gives $x=\mathrm{serialize}(\varphi)$.

**Key facts.** `Std.Sat.CNF.parseClauses_repr`.
