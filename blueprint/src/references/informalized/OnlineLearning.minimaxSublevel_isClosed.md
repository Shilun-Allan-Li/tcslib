<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean :: OnlineLearning.minimaxSublevel_isClosed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closedness of the Minimax Sublevel Set

**Claim.** If $X$ is closed and $x\mapsto f(x,y)$ is continuous on $X$, then the minimax sublevel set at column $y$ and threshold $c$ is closed.

**Proof.** The sublevel set is the intersection of $X$ with the preimage of the closed ray $(-\infty,c]$ under the continuous-on-$X$ map $x\mapsto f(x,y)$. The preimage is closed relative to $X$, and since $X$ itself is closed in $\mathbb R$, this intersection is closed in $\mathbb R$.
