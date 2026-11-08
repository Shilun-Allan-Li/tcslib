<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianConvolution_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution as a Uniform Average

**Claim.** For functions on a finite abelian group, their normalized convolution at $x$ is the uniform average of $f(y)g(x-y)$ over $y\in G$.

**Proof.** Fix $x\in G$. The fiber of the addition map over $x$ consists of pairs $(a,b)$ with $a+b=x$. Each $y\in G$ determines exactly one such pair, $(y,x-y)$, and every pair in the fiber is obtained this way. Thus reindexing the sum defining the discrete convolution by this bijection turns it into $\sum_{y\in G} f(y)g(x-y)$. The normalization in the definition of convolution divides this sum by $|G|$, which is precisely the uniform expectation over $G$.
