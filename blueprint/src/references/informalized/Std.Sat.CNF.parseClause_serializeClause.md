<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClause_serializeClause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Encoding Round Trip

**Claim.** If the encoding of a clause $C$ has length at most $f$, then parsing that encoding followed by $r$ with fuel $f$ returns $C$ and remainder $r$.

**Proof.** Induct on the clause, allowing the fuel to vary. For the empty clause, its encoding is just the terminating false bit, so the parser immediately returns the empty clause and leaves $r$. For a nonempty clause $\ell::C$, fuel zero is impossible because its encoding has positive length. At successor fuel, the length bound implies that the encoding of the tail clause $C$ has length at most the predecessor fuel. The encoding of $\ell::C$ followed by $r$ splits as the literal encoding of $\ell$ followed by the encoding of $C$ and then $r$. Literal parsing recovers $\ell$ and leaves that tail string; the induction hypothesis parses the tail as $C$ with remainder $r$. The clause parser consequently returns $\ell::C$ and $r$.

**Key facts.** `Std.Sat.CNF.parseLit_serializeLit`.
