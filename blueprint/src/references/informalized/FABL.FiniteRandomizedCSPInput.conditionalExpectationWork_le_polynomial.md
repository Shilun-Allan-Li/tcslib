<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.FiniteRandomizedCSPInput.conditionalExpectationWork_le_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound on Conditional-Expectation Work

**Claim.** The total conditional-expectation work is at most $|D|(|D|^r+1)(n+m)^2$, where $n$ is the number of variables, $m$ the number of constraint occurrences, and $r$ the maximum predicate arity.

**Proof.** Set $c=|D|(|D|^r+1)$. For each variable, its step work is $|D|$ times the sum of the table-work costs of constraints containing that variable. Each such table cost is at most $|D|^r+1$: the predicate’s arity is at most the maximum arity (`arity_le_maxArity`), and raising the nonnegative integer $|D|$ to these exponents preserves the inequality. The number of affected constraint occurrences is at most $m$, since they are obtained by filtering the constraint multiset. Thus each variable’s step costs at most $cm$. Summing over the $n$ variables bounds total work by $ncm$. Since $nm\le(n+m)^2$, this is at most $c(n+m)^2$, which is the evaluation of the stated polynomial.

**Key facts.** `FABL.CSPTemplate.arity_le_maxArity`.
