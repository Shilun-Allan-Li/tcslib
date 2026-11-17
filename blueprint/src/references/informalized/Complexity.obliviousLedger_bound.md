<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean :: Complexity.obliviousLedger_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Schedule cost bound

**Claim.** For the stated natural-number bounds on $n$, $\tau$, and $\mathrm{width}$, the schedule-cost expression is at most the claimed quadratic polynomial in $u+1$.

**Proof.** Set $v=(u+1)^2$. Since $u+1\ge1$, we have $u+1\le v$ and $1\le v$. Bound $\tau$ by $b v$, using $\tau\le b(u+1)$ and $u+1\le v$; bound $3n$ by $3v$, using $n\le u$; and bound $18$ by $18v$. For the term multiplied by $u+1$, use $\mathrm{width}\le b(u+1)$ to obtain
\[(u+1)(2\,\mathrm{width}+(a+1)+4)\le 2b v+((a+1)+4)v.\]
Also, $22(a+1)(u+1)\le22(a+1)v$. The final quadratic term is already $18((a+1)(u+1))^2$. Adding these bounds gives the claimed right-hand side: collecting the coefficients yields $18(a+1)^2+23(a+1)+3b+25$, all multiplied by $v$.
