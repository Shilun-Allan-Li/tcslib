<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.anfCoeff_coordinateSum_add_anfMonomial_of_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of a disjoint sum and monomial

**Claim.** If $T$ is nonempty and disjoint from $S$, the algebraic normal form coefficient indexed by $T$ of the sum of the coordinate sum over $S$ and the monomial on $T$ is $1$.

**Proof.** First, the coordinate sum over $S$ agrees with the linear function given by dotting the input with the indicator vector of $S$ (`f₂DotProduct_f₂CubeOfFinset`). Thus the coefficient of the sum is the sum of the corresponding coefficients, by additivity of algebraic normal form coefficients (`anfCoeff_add`). The coefficient of the monomial on $T$ at $T$ is $1$ (`anfCoeff_anfMonomial`). For the linear function, its coefficient at a nonempty set can be nonzero only when that set is a singleton, as described by the affine coefficient formula (`anfCoeff_affineFunction`). If $T$ is a singleton, its coordinate is not in $S$ by disjointness, so the linear contribution is $0$; if $T$ has more than one element, that contribution is also $0$. In either case, adding the monomial's contribution gives $1$.

**Key facts.** `FABL.anfCoeff_add`, `FABL.f₂DotProduct_f₂CubeOfFinset`, `FABL.anfCoeff_affineFunction`, `FABL.f₂CubeOfFinset_apply`, `FABL.anfCoeff_anfMonomial`.
