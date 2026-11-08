<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.influence_le_one_div_sqrt_of_transitiveSymmetric_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound from transitive symmetry

**Claim.** Every monotone, transitive-symmetric Boolean-valued function on the $n$-dimensional cube has influence at most $1/\sqrt n$ at each coordinate.

**Proof.** Let $a$ be the singleton Fourier coefficient at the coordinate under consideration. Transitive symmetry makes every singleton coefficient equal to $a$ (\texttt{FABL.fourierCoeff_singleton_eq_of_transitiveSymmetric}). Monotonicity identifies each singleton coefficient with its corresponding influence (\texttt{FABL.influence_eq_fourierCoeff_singleton_of_monotone}); in particular, $a\geq0$ because influence is nonnegative (\texttt{FABL.influence_nonneg}). Parseval's identity says the sum of the squares of all Fourier coefficients is $1$ (\texttt{FABL.sum_sq_fourierCoeff_eq_one}). The $n$ singleton terms alone therefore contribute $na^2$, and hence $na^2\leq1$. Since $n>0$, this yields $a^2\leq1/n$. Combining this with $a\geq0$ gives $a\leq1/\sqrt n$, which is the desired influence bound.

**Key facts.** `FABL.fourierCoeff_singleton_eq_of_transitiveSymmetric`, `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.influence_nonneg`, `FABL.sum_sq_fourierCoeff_eq_one`.
