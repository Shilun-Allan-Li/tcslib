<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPolyCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on the Loop Cost

**Claim.** For positive $q$ and every natural number $r$, the recursively defined loop cost satisfies $T_r\le (C+1+5r)q^r$.

**Proof.** Use induction on $r$. At $r=0$, the cost is $C+1$, which is exactly the proposed bound. For the step, assume the bound at $r$. The recursion gives $T_{r+1}=q(T_r+2)+q+2$. Substituting the induction bound and distributing yields
\[
T_{r+1}\le (C+1+5r)q^{r+1}+3q+2.
\]
Because $q>0$, we have $q\le q^{r+1}$ and $1\le q^{r+1}$; consequently $3q+2\le 5q^{r+1}$. Absorbing this term gives $T_{r+1}\le (C+1+5(r+1))q^{r+1}$, as required.
