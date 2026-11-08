<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.theorem71_uniformEquicontinuity_of_jointContinuous_compact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Equicontinuity from Compactness

**Claim.** Joint continuity on $X\times Y$, together with compactness of both sets, implies uniform equicontinuity of the payoff in its row variable uniformly over columns.

**Proof.** The product $X\times Y$ is compact. By the Heine–Cantor theorem, the jointly continuous payoff is uniformly continuous on this product. Given $\varepsilon>0$, choose the corresponding product-space distance bound. For two points $(x,y)$ and $(x',y)$ with the same column, their product distance is exactly the distance between $x$ and $x'$. Thus a single radius works for every column, and uniform continuity gives $|f(x,y)-f(x',y)|<\varepsilon$ whenever $x,x'\in X$ are closer than that radius.
