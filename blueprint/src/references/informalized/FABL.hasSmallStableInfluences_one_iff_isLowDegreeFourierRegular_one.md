<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.hasSmallStableInfluences_one_iff_isLowDegreeFourierRegular_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit-parameter influences and first-level regularity

**Claim.** For $0\leq\varepsilon$, all stable influences at parameter $1$ are at most $\varepsilon$ exactly when every nonempty set of at most one coordinate has Fourier coefficient of absolute value at most $\sqrt{\varepsilon}$.

**Proof.** Assume first that all stable influences are at most $\varepsilon$. Any nonempty set of size at most one is a singleton, say $\{i\}$. Its coefficient squared equals the stable influence at parameter zero for coordinate $i$ (`stableInfluence_zero_eq_sq_fourierCoeff_singleton`); the hypothesis bounds this by $\varepsilon$. Since $\varepsilon\geq0$, this implies that the coefficient's absolute value is at most $\sqrt{\varepsilon}$.

Conversely, assume the stated coefficient bounds. For each coordinate $i$, the stable influence at parameter one is the squared Fourier coefficient on $\{i\}$, by the same singleton identity. Squaring the assumed absolute-value bound gives a bound by $(\sqrt{\varepsilon})^2=\varepsilon$, using $\varepsilon\geq0$.

**Key facts.** `FABL.stableInfluence_zero_eq_sq_fourierCoeff_singleton`.
