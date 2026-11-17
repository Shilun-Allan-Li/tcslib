<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/UniversalHashing.lean :: TCSlib.InformationTheory.isUniversal_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universality of Affine Hashes

**Claim.** For a finite field $F$, among the pairs $(a,b)\in F^2$, the fraction for which $ax+b=ay+b$ is at most $1/|F|$ whenever $x\ne y$.

**Proof.** Fix distinct $x,y\in F$. The equality $ax+b=ay+b$ simplifies to $a(x-y)=0$. Since $x-y\ne0$ in a field, this forces $a=0$, while $b$ is unrestricted. Thus the collision set is exactly $\{0\}\times F$, with $|F|$ elements, out of $|F|^2$ seed pairs. Its fraction is therefore $1/|F|$, which gives the claimed upper bound.
