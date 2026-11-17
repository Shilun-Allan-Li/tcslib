<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.linear_iff_character -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear functions are dot products

**Claim.** A function on $(\mathbb Z/k\mathbb Z)^n$ is additive if and only if it is the dot product with some vector in $(\mathbb Z/k\mathbb Z)^n$.

**Proof.** Suppose first that $f$ is additive. Choose the candidate vector $s$ by setting its $i$th coordinate to $f(e_i)$, where $e_i$ is the vector supported at coordinate $i$ with value $1$. Every vector is a sum of its coordinate-supported vectors. Additivity makes $f$ of that sum the sum of the corresponding values; on each coordinate-supported vector, repeated addition gives $f(me_i)=m f(e_i)$. Hence $f(x)=\sum_i s_i x_i=s\cdot x$. Conversely, if $f(x)=s\cdot x$, bilinearity of the dot product gives $f(x+y)=s\cdot(x+y)=s\cdot x+s\cdot y=f(x)+f(y)$ (\texttt{ZkFourier.zkDot\_add\_right}).

**Key facts.** `ZkFourier.zkDot_add_right`.
