<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Norms.lean :: BooleanAnalysis.Hypercontractivity.symmetrization_norm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm inequality under symmetrization

**Claim.** If $X$ and $X'$ are independent identically distributed random variables, $X$ has mean zero and belongs to $L^q$, and $q\ge1$, then for every real $a$, $\|a+X\|_{L^q}\le\|a+X-X'\|_{L^q}$.

**Proof.** Let $\nu$ be the distribution of $X$; then $\nu$ is a probability measure, $X$ belongs to $L^q(\nu)$, and its mean under $\nu$ is zero. Independence and equality in distribution identify the joint law of $(X,X')$ with $\nu\times\nu$. For each fixed $x$, the mean-zero property gives $a+x=\int(a+x-y)\,d\nu(y)$. The integral triangle inequality bounds $|a+x|$ by the mean of $|a+x-y|$. The $L^1$ norm is at most the $L^q$ norm because $q\ge1$ on a probability space, so $|a+x|\le\|y\mapsto a+x-y\|_{L^q(\nu)}$. Integrate this pointwise inequality in $x$ to obtain the desired comparison of $L^q$ norms on $\nu$ and $\nu\times\nu$. This integration follows directly by raising the slice inequality to the $q$th power and integrating when $q<\infty$; when $q=\infty$, the same conclusion follows by taking essential suprema. Finally, the distribution and joint-law identifications transfer the two norms back to the original probability space.
