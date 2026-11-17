<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productVariance_eq_secondMoment_sub_mean_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance from the second moment

**Claim.** For a real-valued function on a finite product space, its variance under the independent product law equals its second moment minus the square of its mean.

**Proof.** Let $m$ be the mean. Expand the centered square pointwise as $f^2-2mf+m^2$. Linearity of expectation gives the expectation of $f^2$, minus $2m$ times the expectation of $f$, plus the expectation of the constant $m^2$ (\texttt{pmfExpectation\_add\_fun}, \texttt{pmfExpectation\_smul\_fun}, and \texttt{pmfExpectation\_const}). Since the expectation of $f$ is $m$ and constants integrate to themselves, this simplifies to the second moment minus $m^2$.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_smul_fun`, `FABL.pmfExpectation_const`.
