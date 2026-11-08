<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.inputSymbol_eq_xhat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at the current position

**Claim.** For a configuration $c$ on input $x$, the symbol read at the input head equals the input symbol represented by $xhat$ at the head’s integer coordinate.

**Proof.** By definition, $RI(c,0)$ is $xhat(x,c.inputPos.val)$. If the head position has value $0$, then the configuration reads no symbol, and $xhat$ also returns none because its coordinate is not at least $1$. Otherwise the position is positive. Since a `Fin` position is at most $|x|+1$, the position is not beyond the right boundary; applying the fact that the input symbol at a position $i+1$ is $x[i]?$, with $i=c.inputPos.val-1$ (`inputSymbol_at`), identifies the read symbol as $x[c.inputPos.val-1]?$. This is exactly the value of $xhat$ at the head coordinate, by its definition.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
