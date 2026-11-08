<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LevelOneInequality.lean :: FABL.excess_abs_linearForm_expect_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected excess of a linear form

**Claim.** For a normalized linear form on the sign cube and $s\ge 1$, the expected positive part $(|L|-s)^+$ is at most $2e^{-s^2/2}$.

**Proof.** Let $X(x)=(|L(x)|-s)^+$. Since the sign cube is finite, $X$ is integrable. The layer-cake formula expresses its expectation as the integral, over $t>0$, of the probability that $X>t$. If $X(x)>t$, then $|L(x)|>s+t$. The Rademacher tail bound for a normalized linear form (\texttt{uniformRademacher\_abs\_linearForm\_gt\_le}) therefore bounds this probability by $2e^{-(s+t)^2/2}$. Because $s\ge1$ and $t>0$, we have $(s+t)^2/2\ge s^2/2+t$, so the probability is at most $2e^{-s^2/2}e^{-t}$. Integrating this bound over $t>0$ gives $2e^{-s^2/2}$, since the integral of $e^{-t}$ there is $1$. Finally, the integral against the uniform measure is the expectation (\texttt{integral\_uniformPMF\_eq\_expect}), yielding the claim.

**Key facts.** `FABL.uniformRademacher_abs_linearForm_gt_le`, `FABL.integral_uniformPMF_eq_expect`.
