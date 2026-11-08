<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.absoluteTail_error_le_nonuniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonuniform Bound for Absolute Tails

**Claim.** If the distribution functions of a probability measure $\nu$ and the standard Gaussian differ at every point by at most $K/(1+|x|^3)$, then their absolute tail probabilities at $t\ge0$ differ by at most $2K/(1+t^3)$.

**Proof.** First apply the assumed distribution-function bound at $t$. Because $t\ge0$, this bounds the difference between the measures of $(-\infty,t]$ by $K/(1+t^3)$. Next apply the corresponding strict distribution-function bound at $-t$; since $|-t|=t$, the difference between the measures of $(-\infty,-t)$ has the same bound. The interval $[-t,t]$ is the difference between $(-\infty,t]$ and $(-\infty,-t)$, for both measures: the latter set is contained in the former. Subtracting these two interval expressions and using the triangle inequality shows that the interval probabilities differ by at most $2K/(1+t^3)$. Finally, absolute tail error is bounded by interval error (\(\texttt{FABL.absoluteTail\_error\_le\_of\_interval\_error}\)), yielding the result.

**Key facts.** `FABL.strictCdfError_le_nonuniform`, `FABL.absoluteTail_error_le_of_interval_error`.
