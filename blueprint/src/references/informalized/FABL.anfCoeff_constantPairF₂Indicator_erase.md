<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.anfCoeff_constantPairF₂Indicator_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient on a punctured full set

**Claim.** For any coordinate $i$, the ANF coefficient indexed by all coordinates except $i$ of the indicator of the zero vector and the all-ones vector is $1$ over $\mathbb F_2$.

**Proof.** By the definition of the ANF coefficient, sum the indicator over the subsets $T$ of the full set with $i$ removed. The empty subset contributes $1$, since its associated cube point is the zero vector. Every nonempty such $T$ contributes $0$: it contains some coordinate, so its cube point is not zero; and it omits $i$, so its cube point is not the all-ones vector. These coordinate facts follow from the defining membership formula for the cube point (`FABL.f₂CubeOfFinset_apply`). Hence only the empty subset contributes, and the coefficient is $1$.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
