<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_polyUnary_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Polynomial Output with Linear Space

**Claim.** For every $C,e\in\mathbb{N}$, some finite Boolean Turing machine outputs $C(|x|+1)^e$ true bits within $c(|x|+1)^{e+1}$ steps on every input $x$, while using at most $c(|x|+1)$ work-tape cells through every time $t$.

**Proof.** Split into $e=0$ and $e=d+1$. When $e=0$, use the machine that outputs the fixed word of $C$ true bits. Its running time has the form $c(|x|+1)$ by the constant-function construction, and its space bound is at most $c$; since $|x|+1\ge 1$, this is at most $c(|x|+1)$. When $e=d+1$, use the catalog machine for unary polynomial output. It produces the required word in $(C+5(d+1)+4)(|x|+1)^{d+1}$ steps and uses at most $5(d+1)(|x|+1)$ space. Increase the time bound to $c(|x|+1)^{d+2}$ and the space bound to $c(|x|+1)$ by choosing $c=C+10(d+1)+4$: the coefficient dominates both previous coefficients, and $|x|+1\ge1$ lets the extra power absorb the smaller time exponent.

**Key facts.** `Turing.FinTM.computesFunInTime_const_spaceUsed`, `Turing.FinTM.f2_catalogPoly_unary_computes`, `Turing.FinTM.f2_poly_space`.
