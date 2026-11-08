<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClauses_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Encoding Round Trip

**Claim.** If the encoding of a formula $\varphi$ has length at most $f$, then parsing that encoding followed by $r$ with fuel $f$ returns $\varphi$ and remainder $r$.

**Proof.** Induct on the formula, allowing the fuel to vary. For the empty formula, its encoding is the terminating false bit, so parsing returns the empty formula and leaves $r$. For a nonempty formula $C::\varphi$, fuel zero is impossible because its encoding has positive length. At successor fuel, the length bound ensures both that the encoding of $C$ fits within the predecessor fuel and that the encoding of $\varphi$ does too. The full input has the form of a leading true marker, followed by the encoding of $C$, followed by the encoding of $\varphi$ and $r$. Clause parsing recovers $C$ and leaves the latter tail; the induction hypothesis then recovers $\varphi$ and leaves $r$. The formula parser therefore returns $C::\varphi$ with remainder $r$.

**Key facts.** `Std.Sat.CNF.parseClause_serializeClause`.
