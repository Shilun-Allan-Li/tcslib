<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.mul_pmfEventProbability_le_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event probability bounded by expectation

**Claim.** For a probability distribution $p$ on a finite set $\Omega$, a nonnegative function $Y:\Omega\to\mathbb R$, and any real $a$, the product of $a$ and the probability of $\{x:a\le Y(x)\}$ is at most the expectation of $Y$.

**Proof.** Write the left-hand side as the expectation of the function $x\mapsto a\,\mathbf 1_{\{a\le Y(x)\}}$. This follows from the definition of event probability as the expectation of its indicator and the fact that multiplying a function by a constant multiplies its expectation by that constant (\texttt{FABL.pmfExpectation\_const\_mul}). Pointwise, if $a\le Y(x)$, then the indicated value is $a$, which is at most $Y(x)$. If $a\not\le Y(x)$, the indicated value is zero, which is at most $Y(x)$ by nonnegativity. Thus the pointwise function is bounded above by $Y$, and monotonicity of expectation gives the claimed inequality (\texttt{FABL.pmfExpectation\_mono}).

**Key facts.** `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_mono`.
