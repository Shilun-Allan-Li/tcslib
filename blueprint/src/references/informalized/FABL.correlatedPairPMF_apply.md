<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedPairPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point probabilities of a correlated pair

**Claim.** For a point pair $(x,y)$, the probability of that pair is the probability of choosing $x$ uniformly from the cube times the noise-kernel probability of producing $y$ from $x$.

**Proof.** Expand the definition of the joint law as a mixture over the initial point $z$, followed by the noise kernel and the map sending the output to $(z,w)$. At the target $(x,y)$, only the summand with $z=x$ can contribute, since the first coordinate must match; within that summand, only the output $w=y$ contributes. The finite sums therefore collapse to the uniform mass at $x$ times the noise-kernel mass at $y$ given $x$, as claimed.
