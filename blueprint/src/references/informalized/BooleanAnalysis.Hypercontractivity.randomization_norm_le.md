<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Norms.lean :: BooleanAnalysis.Hypercontractivity.randomization_norm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random-sign moment comparison

**Claim.** Under the stated hypotheses, the $L^q$ norm of $a+X/2$ is at most the $L^q$ norm of $a+rX$.

**Proof.** Transfer $X$ to its law $\nu$ on $\mathbb R$. This preserves its $L^q$ membership and mean zero. Independence and the fact that $r$ is a fair sign identify the joint law of $(X,r)$ with the product of $\nu$ and the measure putting mass $1/2$ at each of $1$ and $-1$ ($\texttt{IsRademacherRV.map_eq}$). Write $P=\|a+x\|_{L^q(\nu)}$, $M=\|a-x\|_{L^q(\nu)}$, and let $B$ be the $L^q$ norm of $a+yx$ under this product law. The centered mean gives $\int(a-x)\,d\nu=a$. The integral triangle inequality, followed by monotonicity of norms on a probability space for $q\ge1$, therefore gives $|a|\le M$. Since $a+x/2$ is the average of $a+x$ and the constant function $a$, the norm triangle inequality and homogeneity yield $\|a+x/2\|_{L^q(\nu)}\le (P+M)/2$. It remains to bound this average by $B$. If $q=\infty$, almost every pair $(x,y)$ has $|a+yx|\le B$; taking the two sign values shows that both profiles $a+x$ and $a-x$ are essentially bounded by $B$, so $P,M\le B$. If $q<\infty$, integrating $|a+yx|^q$ first over the two equally likely signs gives $B^q=(P^q+M^q)/2$. The power mean inequality for $q\ge1$ implies $((P+M)/2)^q\le(P^q+M^q)/2$, hence $(P+M)/2\le B$. Combining these bounds proves the claim under $\nu$. Finally, mapping the original space to the law of $X$, and mapping the joint variable to the function $(x,y)\mapsto a+yx$, transfers the inequality back to $\mu$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.IsRademacherRV.map_eq`.
