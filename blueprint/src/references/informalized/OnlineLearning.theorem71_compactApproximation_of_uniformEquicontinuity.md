<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.theorem71_compactApproximation_of_uniformEquicontinuity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compact Approximation from Uniform Equicontinuity

**Claim.** Under the stated convex-compact minimax hypotheses and uniform equicontinuity in the row variable, every positive tolerance admits a nonempty finite row sample whose lower value is at most the full lower value plus that tolerance.

**Proof.** Fix $\varepsilon>0$, and write $C=\sup_{y\in Y}\inf_{x\in X}f(x,y)$. Uniform equicontinuity supplies a radius $\rho>0$ such that changing the row by distance less than $\rho$ changes any payoff by less than $\varepsilon/2$. Compactness of $X$ gives a finite cover by radius-$\rho$ balls centered at points of $X$; use those centers as the sample. The sample is nonempty because $X$ is nonempty.

For each fixed $y\in Y$, its infimum over $X$ is at most $C$, so there is a row $x_0\in X$ with $f(x_0,y)<C+\varepsilon/2$. Choose a sample center within distance $\rho$ of $x_0$. Uniform equicontinuity makes that center's payoff less than $C+\varepsilon$. Thus the infimum over the finite sample is at most $C+\varepsilon$ for every $y$. Taking the supremum over $Y$ proves the required bound.
