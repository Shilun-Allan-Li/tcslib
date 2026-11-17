<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.productMean_diagonal_section -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a diagonal section

**Claim.** Under the stated coordinate-invariance condition, the product mean of $x\mapsto h(x_j,x)$ equals the mean over $\omega$ of the product means of $x\mapsto h(\omega,x)$.

**Proof.** Let $d(x)=h(x_j,x)$. First project $d$ onto all coordinates except $j$. The projection theorem for the finite orthonormal basis containing the constant function says that this does not change its product mean (\texttt{FiniteFourierBasis.productMean_projectOnCoordinates}). By the coordinate projection formula (\texttt{coordinateProjection_apply}), the projected function at $x$ is the $\pi$-mean of $\omega\mapsto d(\operatorname{replaceCoordinate}(x,j,\omega))$. Replacing coordinate $j$ by $\omega$ makes the $j$th coordinate equal to $\omega$, and the assumed invariance of $h$ therefore identifies this integrand with $h(\omega,x)$. Thus the original product mean equals the product mean of $x\mapsto \mathbb E_{\omega\sim\pi}[h(\omega,x)]$. Finally, interchange the two finite expectations using commutation of expectations (\texttt{pmfExpectation_comm}); the result is the $\pi$-mean of the product means of the sections $h(\omega,\cdot)$.

**Key facts.** `FABL.FiniteFourierBasis.productMean_projectOnCoordinates`, `FABL.coordinateProjection_apply`, `FABL.pmfExpectation_comm`.
