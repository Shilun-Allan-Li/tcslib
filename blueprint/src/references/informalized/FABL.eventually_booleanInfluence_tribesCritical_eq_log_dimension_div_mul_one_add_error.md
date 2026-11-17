<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.eventually_booleanInfluence_tribesCritical_eq_log_dimension_div_mul_one_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical tribes coordinate influence

**Claim.** For all sufficiently large $w$, every coordinate influence of the critical tribes function equals $\frac{\ln d}{d}(1+e_w)$, where $d$ is its dimension and $e_w$ is the specified relative error.

**Proof.** Take $w$ sufficiently large that $w\ge 1$ and the critical dimension $d$ is greater than $1$. The coordinate influence theorem identifies the influence at any coordinate with the common value of the critical tribes coordinate influence ($\texttt{booleanInfluence\_tribesCritical}$). By the definition of the relative error, that common value is $\frac{\ln d}{d}(1+e_w)$: multiplying out the right-hand side cancels the denominator $\ln d$ in the error term. These cancellations are valid because $d>0$ and $\ln d>0$.

**Key facts.** `FABL.booleanInfluence_tribesCritical`, `FABL.tendsto_tribesCriticalDimension_atTop`.
