<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/UniversalHashing.lean :: TCSlib.InformationTheory.sum_sq_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Sums Over Fibers

**Claim.** For finite sets $A,B$, a map $g:A\to B$, and weights $w:A\to\mathbb R$, the sum over $B$ of the squared sums of weights in each fiber equals the sum over pairs $(x,x')$ whose images under $g$ agree, weighted by $w(x)w(x')$.

**Proof.** For each $y\in B$, rewrite the sum over the fiber $g(x)=y$ as $\sum_{x\in A} \mathbf{1}_{g(x)=y}w(x)$. Squaring and expanding the product of sums gives a sum over pairs $(x,x')$ of $\mathbf{1}_{g(x)=y}\mathbf{1}_{g(x')=y}w(x)w(x')$. Interchange the finite sums over $y,x,x'$. For fixed $x,x'$, the inner sum over $y$ contributes once precisely when both equalities $g(x)=y$ and $g(x')=y$ hold, which is equivalent to $g(x)=g(x')$; otherwise it contributes zero. This yields the stated expression.
