<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/BentDegree.lean :: FABL.even_scaled_restrictionFourierCoeff_of_isBent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Scaling of Restricted Coefficients

**Claim.** Under the bentness assumption and a nonempty set of fixed coordinates, each restricted Fourier coefficient indexed by $A$ is an even integer multiple of $2^{-\lfloor n/2\rfloor}$.

**Proof.** Write $s=2^{-\lfloor n/2\rfloor}$. For each frequency $T$ on the fixed coordinates, combine its lifted frequency with the lift of $A$. Bentness says the resulting ambient Fourier coefficient has absolute value $s$: translate the frequency to its binary-cube index and use `vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`. The corresponding monomial on the fixed signs has square one (`indexedMonomial_sq`), hence absolute value one. Thus their product has absolute value $s$ and is either $s$ or $-s$. Assign to each $T$ the integer sign $+1$ in the first case and $-1$ in the second; each summand is that sign times $s$.

Let $q$ be the sum of these signs over all subsets $T$ of the fixed-coordinate index set. Modulo two, both signs are $1$, so $q$ reduces to the number of such subsets. If the fixed-coordinate index set has positive cardinality, its powerset has cardinality a positive power of two, which is even. Hence $q$ is even. Finally, the restricted Fourier coefficient is the sum of the ambient coefficients weighted by these monomials (`restrictionFourierCoeff_eq_sum`). Replacing each summand by its sign times $s$ identifies this sum with $q s$, as required.

**Key facts.** `FABL.indexedMonomial_sq`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.restrictionFourierCoeff_eq_sum`.
