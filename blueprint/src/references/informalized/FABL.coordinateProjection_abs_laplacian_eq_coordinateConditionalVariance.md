<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.coordinateProjection_abs_laplacian_eq_coordinateConditionalVariance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projected absolute Laplacian and conditional variance

**Claim.** For a function taking values in $\{-1,1\}$, projecting the pointwise absolute coordinate Laplacian onto all coordinates except one gives its conditional variance in that coordinate.

**Proof.** Fix an input $x$ and write $z(\omega)=f(x_{i\leftarrow\omega})$, where $x_{i\leftarrow\omega}$ is obtained by replacing coordinate $i$ by $\omega$. By the coordinate projection formula (\texttt{FABL.coordinateProjection\_apply}), the projected absolute Laplacian is the expectation over $\omega$ of the absolute difference between $z(\omega)$ and the coordinate projection of $f$ at $x_{i\leftarrow\omega}$. The coordinate projection is unchanged by replacing coordinate $i$ (\texttt{FABL.coordinateProjection\_replaceCoordinate}), and its value at $x$ is the mean $\mathbb E_\pi z$ by the same projection formula. The expression is therefore $\mathbb E_\pi|z-\mathbb E_\pi z|$. Since $z$ takes only the values $-1$ and $1$, its mean absolute deviation equals its variance, by the sign-valued expectation identity (\texttt{FABL.pmfExpectation\_abs\_sub\_mean\_eq\_variance\_of\_hasSignRange}). This variance is exactly the conditional variance at $x$, proving equality pointwise.

**Key facts.** `FABL.coordinateProjection_apply`, `FABL.coordinateProjection_replaceCoordinate`, `FABL.pmfExpectation_abs_sub_mean_eq_variance_of_hasSignRange`.
