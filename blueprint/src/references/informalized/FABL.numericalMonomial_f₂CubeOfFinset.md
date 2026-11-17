<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalMonomial_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Numerical monomial on an indicator vector

**Claim.** The numerical monomial indexed by $S$, evaluated at the binary vector equal to $1$ exactly on $U$, is $1$ if $S\subseteq U$ and $0$ otherwise.

**Proof.** If $S\subseteq U$, every coordinate indexed by $S$ has value $1$ in the indicator vector (`f₂CubeOfFinset_apply`), so every factor in the product is $1$ and the monomial equals $1$. If $S\nsubseteq U$, choose a coordinate in $S$ but outside $U$. Its factor is $0$, so the product vanishes. These two cases give the stated value.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
