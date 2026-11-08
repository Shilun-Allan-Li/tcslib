<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClauses_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation of a Parsed Formula

**Claim.** If parsing a bit string $x$ as a formula with fuel $f$ returns formula $\varphi$ and remainder $r$, then $x$ is the encoding of $\varphi$ followed by $r$.

**Proof.** Induct on the fuel, generalizing the input, formula, and remainder. At fuel zero, a successful parse is possible only when the input begins with false; it returns the empty formula and leaves the tail, giving exactly the formula encoding followed by that remainder. The same case handles a leading false at successor fuel, while an empty input or a leading true at zero fuel cannot succeed. At successor fuel with a leading true, success requires a clause parse from the tail, returning $C$ and an intermediate remainder $t$, followed by a formula parse from $t$, returning $\psi$ and $r$. The successful result identifies $\varphi=C::\psi$. By clause representation, the original tail is the encoding of $C$ followed by $t$; by the induction hypothesis, $t$ is the encoding of $\psi$ followed by $r$. Including the initial true marker gives precisely the encoding of $C::\psi$ followed by $r$.

**Key facts.** `Std.Sat.CNF.parseClause_repr`.
