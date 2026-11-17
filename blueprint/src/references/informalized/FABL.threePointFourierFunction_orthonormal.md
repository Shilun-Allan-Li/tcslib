<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.threePointFourierFunction_orthonormal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthonormality of the Three-Point Basis

**Claim.** Under the uniform probability measure on $\{a,b,c\}$, the specified three functions are orthonormal: the expected product of the functions indexed by $a,b\in\{0,1,2\}$ is $1$ if $a=b$ and $0$ otherwise.

**Proof.** The uniform-expectation identity (\texttt{pmfExpectation\_uniformPMF\_eq\_expect}) reduces the assertion to averaging the product of the two functions over the three points. Reindex the average by $0,1,2$, corresponding respectively to $a,b,c$, and compute for each pair of indices. When both indices are $0$, the product is constantly $1$. For index $1$ with itself, the average is $(2+1/2+1/2)/3=1$; for index $2$ with itself it is $(0+6/4+6/4)/3=1$. The mixed averages vanish: the constant function paired with either nonconstant function has values summing to zero, and the product of functions $1$ and $2$ is zero at $a$ while its values at $b$ and $c$ cancel. Hence the expected product is precisely the Kronecker delta.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
