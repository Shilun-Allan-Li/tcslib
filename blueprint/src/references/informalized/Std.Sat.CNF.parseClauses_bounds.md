<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseClauses_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for a Successful Formula Parse

**Claim.** If parsing $x$ with fuel $f$ returns formula $\varphi$ and remainder $r$, then $|r|\le |x|$, and each literal $(v,b)$ in each clause of $\varphi$ satisfies $v+1+|r|\le |x|$.

**Proof.** Induct on the fuel, generalizing the input, formula, and remainder. At zero fuel, a successful parse can only begin with false: it returns the empty formula and leaves the tail as remainder. Thus the remainder is shorter than the input, and the assertion about formula literals is vacuous. The same reasoning applies at successor fuel when the input begins with false; empty inputs and inputs beginning with true cannot succeed through that branch. In the remaining case the input begins with true. Success requires parsing a clause from its tail $s$, yielding clause $D$ and remainder $t$, then parsing the remaining formula from $t$, yielding $\psi$ and remainder $r$. The clause bounds give $|t|\le |s|$ and $v+1+|t|\le |s|$ for literals in $D$; the induction hypothesis gives $|r|\le |t|$ and the corresponding bounds for literals in $\psi$. Since $|x|=|s|+1$ and the result formula is $D::\psi$, these inequalities imply both the remainder bound and the required literal bound for every clause of the result.

**Key facts.** `Std.Sat.CNF.parseClause_bounds`.
