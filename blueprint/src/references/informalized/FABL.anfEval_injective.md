<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfEval_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of ANF coefficients

**Claim.** If two algebraic normal forms agree at every point of the Boolean cube, then their coefficient families agree.

**Proof.** For each coordinate set $U$, evaluate both forms at the point that is $1$ on $U$ and $0$ outside it. The monomial indexed by $S$ is $1$ there exactly when $S\subseteq U$, and is $0$ otherwise; thus equality of the evaluations gives equality of the sums of coefficients over all $S\subseteq U$. The uniqueness theorem for coefficients from all such subset sums (`anfCoeff_unique_of_powerset_sum`) then implies that the two coefficient families are equal.

**Key facts.** `FABL.anfEval_f₂CubeOfFinset`, `FABL.anfCoeff_unique_of_powerset_sum`.
