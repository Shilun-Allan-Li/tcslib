<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.relativeHammingDist_f₂DotProduct_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Between Linear Boolean Forms

**Claim.** For any $a,b\in\mathbb F_2^n$, the relative Hamming distance between $x\mapsto a\cdot x$ and $x\mapsto b\cdot x$ is $0$ if $a=b$, and $1/2$ otherwise.

**Proof.** Rewrite relative Hamming distance as the uniform probability that the two values differ (\(\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}\)). By bilinearity of the dot product, the two values differ precisely when $(a+b)\cdot x\ne 0$: over $\mathbb F_2$, equality of the original values is equivalent to their sum being zero. The uniform probability that a dot product with coefficient vector $\gamma$ is nonzero is $0$ when $\gamma=0$ and $1/2$ otherwise (\(\texttt{uniformProbability\_f₂DotProduct\_ne\_zero}\)). Finally, $a+b=0$ is equivalent to $a=b$, since every element of $\mathbb F_2$ is its own additive inverse. Substituting $\gamma=a+b$ yields the stated cases.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.uniformProbability_f₂DotProduct_ne_zero`.
