<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.IsFourierRegular.leadingCoordinateTimes_of_isBalanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regularity After Adjoining a Coordinate

**Claim.** If $g$ is balanced and all its nonempty Fourier coefficients have absolute value at most $\varepsilon$, then the function formed by multiplying a new leading coordinate by $g$ on the remaining coordinates has the same Fourier regularity bound.

**Proof.** Take any nonempty frequency set $T$ in the enlarged cube and split according to whether it contains the new coordinate $0$. If it does, write it as $T=\{0\}\cup\operatorname{tail}(S)$, where $S$ is its frequency on the remaining coordinates. The Fourier coefficient of the enlarged function at this set equals the coefficient of $g$ at $S$ (\texttt{fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency}). If $S$ is nonempty, its absolute value is at most $\varepsilon$ by regularity of $g$. If $S$ is empty, the coefficient is zero because balance is equivalent to the empty-set Fourier coefficient being zero (\texttt{isBalanced_iff_fourierCoeff_empty_eq_zero}); this too is bounded by the nonnegative $\varepsilon$. If instead $T$ omits $0$, it is the tail of a frequency set $S$, and the enlarged function's coefficient there is zero (\texttt{fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero}), again bounded in absolute value by $\varepsilon$. These cases cover every nonempty $T$.

**Key facts.** `FABL.insert_zero_tailFrequency_frequencyTail_eq`, `FABL.fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency`, `FABL.isBalanced_iff_fourierCoeff_empty_eq_zero`, `FABL.tailFrequency_frequencyTail_eq`, `FABL.fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero`.
