<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_adaptive_midpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adaptive midpoint bound for average length

**Claim.** Under the stated assumptions on $P$, the symmetric average length at $(t,c)$ is at most the average of its values at $(1,c+((1-t)b)^2)$ and $(2t-1,c+((1-t)b)^2)$.

**Proof.** First establish a midpoint estimate that carries the fixed clock $c$ as an extra Euclidean coordinate. For a midpoint $z$ and displacement $d$ with $z+d,z-d\in[0,1]$, these endpoints imply $z\in[0,1]$. Apply the assumed inequality to $P(z)$ and the two endpoint values, then apply the carried midpoint inequality (`carried_midpoint`) to the vectors formed by adjoining $\sqrt c$ to the original vector and adjoining $0$ to its displacement vector. The added coordinate contributes $c$ to all three squared lengths, yielding the same estimate with the clock included.

Apply this estimate first at midpoint $a+tb$, displacement $(1-t)b$, and vectors $u+tv$ and $(1-t)v$. Its endpoints are $a+b$ and $a+(2t-1)b$; they lie in $[0,1]$ by the hypotheses and the interval interpolation fact (`probability_mem`). Apply it again at midpoint $a-tb$ with the same displacement and vectors $u-tv$ and $(1-t)v$. Its endpoints are $a-(2t-1)b$ and $a-b$, again in the interval by `probability_mem`. The two resulting inequalities bound the two square-root terms defining the symmetric average length. Adding them and rearranging gives the average of the lengths at displacements $1$ and $2t-1$, with common clock $c+((1-t)b)^2$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.carried_midpoint`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.probability_mem`.
