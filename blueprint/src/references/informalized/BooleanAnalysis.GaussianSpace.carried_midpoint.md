<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.carried_midpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euclidean midpoint inequality

**Claim.** For vectors $u,v\in\mathbb R^m$ and real numbers $A,B,C$ with $A\ge0$ and $A\le(B+C)/2$, the stated square root involving $A$ and $u$ is at most the average of the two square roots involving $B,u+v$ and $C,u-v$.

**Proof.** Form vectors in $\mathbb R^{m+1}$ by adjoining first coordinates: let $p=(B,u+v)$, $q=(C,u-v)$, and $w=((B+C)/2,u)$. Coordinatewise, $w=(p+q)/2$. The triangle inequality for the Euclidean norm therefore gives $\|w\|\le(\|p\|+\|q\|)/2$. Since $0\le A\le(B+C)/2$, squaring preserves the order and gives $A^2\le((B+C)/2)^2$. Adding $\sum_j u_j^2$ to both sides and taking nonnegative square roots bounds the desired left side by $\|w\|$. The norms of $p$ and $q$ are exactly the two square roots on the right, proving the result.
