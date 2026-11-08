<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicativity Under Random Restrictions

**Claim.** For $0\le\delta_1,\delta_2\le1$, the switching-failure probability at parameter $\delta_1\delta_2$ equals the average over first restrictions at parameter $\delta_1$ of the switching-failure probabilities at parameter $\delta_2$ for the corresponding functions on the free coordinates.

**Proof.** The hypotheses ensure that the product parameter is nonnegative and at most one: nonnegativity follows by multiplying the lower bounds, and $\delta_1\delta_2\le1$ follows from $\delta_1\le1$ and $\delta_2\le1$. The claimed identity is precisely the algebraic restriction-composition identity (\texttt{switchingFailureProbability\_mul\_algebraic}), which applies to all real parameters; the bounds are not needed for that identity.

**Key facts.** `FABL.switchingFailureProbability_mul_algebraic`.
