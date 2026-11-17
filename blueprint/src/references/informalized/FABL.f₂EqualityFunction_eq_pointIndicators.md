<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Interpolation.lean :: FABL.f₂EqualityFunction_eq_pointIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality function and point indicators

**Claim.** For positive $n$, the equality function at $x\in\mathbb F_2^n$ is the sum of the point indicators of the zero and one vectors.

**Proof.** Each point indicator is $1$ precisely when its input equals the indicated point, and is $0$ otherwise ($\texttt{f₂PointIndicator\_eq\_ite}$). First, the zero and one vectors are distinct: since $n>0$, there is a coordinate at which their values differ. If all coordinates of $x$ are equal, the characterization of constant vectors over $\mathbb F_2$ shows that $x$ is either the zero vector or the one vector ($\texttt{forall\_coordinate\_eq\_iff\_eq\_zero\_or\_eq\_one}$). In either case exactly one of the two point indicators is $1$, so their sum is $1$, matching the equality function. If the coordinates are not all equal, $x$ is neither constant zero nor constant one. Both point indicators then vanish, and their sum is $0$, again matching the equality function.

**Key facts.** `FABL.f₂PointIndicator_eq_ite`, `FABL.forall_coordinate_eq_iff_eq_zero_or_eq_one`.
