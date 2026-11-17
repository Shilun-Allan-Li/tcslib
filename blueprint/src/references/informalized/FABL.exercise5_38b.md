<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.exercise5_38b -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared lower-bound comparison

**Claim.** If $1\le C$, $0<\delta$, and $\delta\le1/(10C)$, then $1-\delta-16C^2\delta^2\log_2(1/(C\delta))\ge(1-\delta/2-2\eta(C,\delta))^2$.

**Proof.** Set $x=C\delta$, $L=\log_2(1/x)$, and $\eta=16x^2L$. Then $0<x\le1/10$, and $\delta\le x$. In particular $1/x\ge10>2$, so monotonicity of the base-two logarithm gives $L\ge\log_2 2=1$. Thus the maximum in the definition of $\eta(C,\delta)$ equals $L$, and $\eta(C,\delta)=\eta\ge0$.

We compare the two sides by expanding the square. The left side, in these variables, is $1-\delta-\eta$. The right side is $1-\delta-4\eta+\delta^2/4+2\delta\eta+4\eta^2$. Hence it is enough to show $\delta^2/4+2\delta\eta+4\eta^2\le3\eta$.

First, $C\ge1$ and $L\ge1$ imply $\delta^2/4\le\eta/64$. Next, the bound $x\log_2(1/x)<1/3$ for $0<x\le1/10$ (\texttt{FABL.mul\_logb\_two\_inv\_lt\_one\_third}) gives $\eta=16x\bigl(x\log_2(1/x)\bigr)<16x/3\le8/15<16/25$. Since also $\delta\le1/10$, we obtain $2\delta\eta\le\eta/5$ and $4\eta^2\le(64/25)\eta$. Adding these three estimates bounds the expanded error by $(1/64+1/5+64/25)\eta<3\eta$. Substitution into the expansion proves the desired comparison.

**Key facts.** `FABL.mul_logb_two_inv_lt_one_third`.
