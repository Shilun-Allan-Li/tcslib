<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClause_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation of a Parsed Clause

**Claim.** If parsing a bit string $x$ as a clause with fuel $f$ returns clause $C$ and remainder $r$, then $x$ is the encoding of $C$ followed by $r$.

**Proof.** Proceed by induction on the fuel, generalizing the input, clause, and remainder. At fuel zero, an empty input cannot parse; an input beginning with false parses only as the empty clause, and its input is exactly the empty-clause encoding followed by the remainder. An input beginning with true cannot parse at zero fuel. For successor fuel, the same cases handle empty input and a leading false. If the input begins with true and parsing succeeds, the literal parser must return some literal $\ell$ and tail $t$, and the recursive clause parser must return some clause $D$ and remainder $r$. The successful result therefore identifies $C=\ell::D$ and fixes the final remainder. By literal representation, the initial input is the encoding of $\ell$ followed by $t$; by the induction hypothesis, $t$ is the encoding of $D$ followed by $r$. Concatenating these descriptions gives the encoding of $\ell::D$ followed by $r$.

**Key facts.** `Std.Sat.CNF.parseLit_repr`.
