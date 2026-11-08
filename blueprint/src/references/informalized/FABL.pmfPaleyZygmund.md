<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfPaleyZygmund -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paley–Zygmund Inequality

**Claim.** For a finite set with probability mass function $p$, a nonnegative function $Y$, and $0\leq\theta<1$, one has $(1-\theta)^2(\mathbb{E}_pY)^2\leq\mathbb{P}_p(Y>\theta\mathbb{E}_pY)\,\mathbb{E}_p(Y^2)$.

**Proof.** 1. Set $m=\mathbb{E}_pY$ and let $I(x)$ be the indicator of the event $Y(x)>\theta m$. Nonnegativity of $Y$ gives $m\geq0$ (\texttt{FABL.pmfExpectation_nonneg}). Pointwise, $Y(x)\leq\theta m+Y(x)I(x)$: on the event this follows from $\theta m\geq0$, and off the event it follows from $Y(x)\leq\theta m$. Taking expectations, using monotonicity and the expectation rules for sums and constants (\texttt{FABL.pmfExpectation_mono}, \texttt{FABL.pmfExpectation_add}, and \texttt{FABL.pmfExpectation_const}), yields $m\leq\theta m+\mathbb{E}_p(YI)$. Thus $(1-\theta)m\leq\mathbb{E}_p(YI)$.

2. Both sides of this last inequality are nonnegative: the left by $m\geq0$ and $\theta<1$, and the right because $YI\geq0$. Squaring therefore preserves the inequality. The Cauchy–Schwarz inequality for finite probability expectations, in the form $\mathbb{E}_p(YI)^2\leq\mathbb{E}_p(Y^2)\mathbb{E}_p(I^2)$ (\texttt{FABL.pmfExpectation_mul_sq_le_sq_mul_sq}), bounds the resulting right side. Since $I^2=I$, its expectation is the event probability by the definitions. Finally, rearranging the product and using $((1-\theta)m)^2=(1-\theta)^2m^2$ gives the claimed bound.

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mul_sq_le_sq_mul_sq`.
