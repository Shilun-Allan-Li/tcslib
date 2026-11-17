<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.vectorFourierWeightAbove_le_expect_sq_sub_of_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier tail bounded by squared error

**Claim.** If $g$ has Fourier degree at most $k$, then the Fourier weight of $f$ above degree $k$ is at most the uniform average of $(f-g)^2$.

**Proof.** Set $r(x)=f(x)-g(x)$. For every index $\gamma$ with support size greater than $k$, the degree hypothesis implies that the coefficient of $g$ at $\gamma$ vanishes (\texttt{vectorFourierDegree\_le\_iff}). By linearity of Fourier coefficients under subtraction (\texttt{vectorFourierCoeff\_sub}), the coefficient of $r$ there therefore equals the coefficient of $f$. Thus the tail sum for $f$ is the sum of squared coefficients of $r$ over those indices. Since squares are nonnegative, this restricted sum is at most the sum over all indices. Plancherel's identity (\texttt{vector\_plancherel}), applied to $r$ with itself, identifies the full sum of squared coefficients with the average of $r(x)^2$. Substituting the definition of $r$ yields the stated bound.

**Key facts.** `FABL.vectorFourierDegree_le_iff`, `FABL.F₂DecisionTree.vectorFourierCoeff_sub`, `FABL.vector_plancherel`.
