<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.multichoose_one_half_eq_centralBinom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Parameter Multichoose Formula

**Claim.** For every natural number $n$, the generalized binomial coefficient with parameter $1/2$ equals the central binomial coefficient divided by $2^{2n}$.

**Proof.** We use induction on $n$. The case $n=0$ follows since both sides are $1$. For the step from $n$ to $n+1$, the rising-factorial identity for multichoose coefficients says that multiplying the coefficient of order $n+1$ by $(n+1)!$ gives the rising factorial obtained by appending the factor $1/2+n$. Applying the same identity at order $n$ and canceling the nonzero factor $n!$ yields
\[
(n+1)\binom{1/2+n}{n+1}_{\!\mathrm{gen}}=(n+1/2)\binom{1/2+n-1}{n}_{\!\mathrm{gen}},
\]
where the generalized coefficients denote the corresponding `Ring.multichoose` values. Substitute the induction hypothesis on the right. The central binomial coefficients satisfy the recurrence
\[
(n+1)\binom{2n+2}{n+1}=2(2n+1)\binom{2n}{n},
\]
which follows from the recurrence for central binomial coefficients. Also $2^{2n+2}=4\cdot 2^{2n}$. These two recurrences show that the proposed value at order $n+1$ satisfies the same relation as the multichoose coefficient. Since $n+1$ is nonzero, cancellation gives the desired formula.
