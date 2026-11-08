<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.numVars_decode_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable count of a decoded formula

**Claim.** For every finite bit string $x$, the variable count of the CNF formula obtained by decoding $x$ is at most the length of $x$.

**Proof.** Unfold decoding and parsing, and inspect the result of parsing all of $x$. If parsing fails, or succeeds with a nonempty remainder, decoding returns the empty fallback formula, whose variable count is zero and hence is at most $|x|$. In the remaining case parsing returns $(\varphi,[])$, so decoding returns $\varphi$. The successful-parse bounds (`Std.Sat.CNF.parseClauses_bounds`) say that each literal $(v,b)$ in each clause of $\varphi$ satisfies $v+1+|[]|\le |x|$, hence $v+1\le |x|$. The variable-count bound from literal bounds (`Std.Sat.CNF.numVars_le_of_literal_bounds`) now gives $N(\varphi)\le |x|$.

**Key facts.** `Std.Sat.CNF.parseClauses_bounds`, `Std.Sat.CNF.numVars_le_of_literal_bounds`.
