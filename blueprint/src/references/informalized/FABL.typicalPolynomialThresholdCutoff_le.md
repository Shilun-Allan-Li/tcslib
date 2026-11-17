<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.typicalPolynomialThresholdCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Typical polynomial cutoff bound

**Claim.** For every integer $n\ge 2$, the typical polynomial cutoff $K_n$ is at most $\frac n2+2\sqrt{n\log n}$.

**Proof.** Write the real number whose floor defines $K_n$ as $\frac n2+\frac n2\sqrt{2\log(48n)/n}$. Since $n\ge2$, both logarithms involved are nonnegative, so the square roots are defined and nonnegative. The floor is no larger than its argument; it remains to bound the second summand. Squaring the two nonnegative sides reduces this to an algebraic comparison. The estimate $\log(48n)\le 7\log n$ (\texttt{FABL.log\_48\_mul\_le\_seven\_log}) supplies the needed logarithmic bound; after clearing the positive factors, the comparison follows from $n\ge2$. Thus the deviation term is at most $2\sqrt{n\log n}$, and adding $n/2$ proves the result.

**Key facts.** `FABL.log_48_mul_le_seven_log`.
