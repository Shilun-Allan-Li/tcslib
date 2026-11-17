<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.abs_pmfExpectation_rpow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power of an Absolute Expectation

**Claim.** For a probability mass function $\pi$ on a finite set, a real $p\geq1$, and a real-valued function $f$, one has $|\mathbb E_\pi f|^p\leq\mathbb E_\pi(|f|^p)$.

**Proof.** First, the triangle inequality for finite sums and nonnegativity of the probability weights give $|\mathbb E_\pi f|\leq\mathbb E_\pi|f|$. Raising both nonnegative sides to the power $p\geq1$ preserves the inequality. Next apply Jensen's inequality to the convex function $u\mapsto u^p$ on $[0,\infty)$, with weights $\pi(x)$ and values $|f(x)|$. The weights are nonnegative and sum to $1$, as expressed by the fact that the expectation of the constant function $1$ is $1$ (\(\texttt{FABL.pmfExpectation_const_one}\)). Jensen's inequality therefore yields $(\mathbb E_\pi|f|)^p\leq\mathbb E_\pi(|f|^p)$. Combining the two inequalities proves the result.

**Key facts.** `FABL.pmfExpectation_const_one`.
