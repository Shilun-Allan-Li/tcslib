<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.coordinateProjection_resamplingDisagreement_eq_half_variance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resampling disagreement and conditional variance

**Claim.** For a sign-valued function, projecting the probability that resampling coordinate $i$ changes its value gives one half of the conditional variance in coordinate $i$.

**Proof.** Fix an input $x$ and put $z(\omega)=f(x_{i\leftarrow\omega})$. The coordinate projection formula (\texttt{FABL.coordinateProjection\_apply}) expresses the left side as an outer average over a resampled value $\omega'$ of the disagreement probability between $f(x_{i\leftarrow\omega'})$ and the function evaluated after another replacement. Replacing coordinate $i$ twice leaves the final input equal to $x_{i\leftarrow\omega}$, so this is the probability that $z(\omega')\ne z(\omega)$. The function $z$ still takes only the values $-1$ and $1$. For two independent samples from a sign-valued function, the probability of disagreement is half its variance (\texttt{FABL.pmfExpectation\_independent\_disagreement\_eq\_half\_variance}). Applying this identity gives one half of the variance of $z$, which is the conditional variance at $x$.

**Key facts.** `FABL.coordinateProjection_apply`, `FABL.pmfExpectation_independent_disagreement_eq_half_variance`.
