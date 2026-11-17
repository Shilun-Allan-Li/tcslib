<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.anfCoeff_firstCoordinateSlice_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of the one-coordinate slice

**Claim.** The coefficient at $S$ of the slice with first coordinate $1$ is the sum in $\mathbb F_2$ of the coefficients of $f$ at the tail set $S^+$ and at $S^+\cup\{0\}$.

**Proof.** The tail set $S^+$ does not contain coordinate $0$ (`zero_notMem_tailFrequency`). Its subsets therefore split into those not containing $0$ and those obtained by adjoining $0$. The sum over the first family is the coefficient of the slice with first coordinate $0$ (`anfCoeff_firstCoordinateSlice_zero`). The sum over the second family is the coefficient of the slice with first coordinate $1$: the tail-set correspondence is bijective on subsets, and adjoining $0$ to the indicator cube gives the cube whose first coordinate is $1$ and whose tail is the original indicator cube (`f₂CubeOfFinset_insert_zero_tailFrequency`). Hence the coefficient at $S^+\cup\{0\}$ is the sum of the two slice coefficients. Substituting the zero-slice identity and cancelling the repeated zero-slice coefficient in characteristic two leaves the claimed formula.

**Key facts.** `FABL.zero_notMem_tailFrequency`, `FABL.anfCoeff_firstCoordinateSlice_zero`, `FABL.f₂CubeOfFinset_insert_zero_tailFrequency`.
