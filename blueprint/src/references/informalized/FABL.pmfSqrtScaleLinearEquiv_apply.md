<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfSqrtScaleLinearEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-Root Scaling Coordinates

**Claim.** For a finite set, a probability mass function $\pi$ with nonzero mass at every point, and $f:\Omega\to\mathbb{R}$, the $x$-coordinate of the square-root scaling of $f$ is $\sqrt{\pi(x)}f(x)$.

**Proof.** The scaling map is defined coordinatewise by multiplying each coordinate of $f$ by $\sqrt{(\pi(x)).\mathrm{toReal}}$, followed by the canonical identification with Euclidean space. Evaluating the composite map at coordinate $x$ therefore gives exactly $\sqrt{(\pi(x)).\mathrm{toReal}}f(x)$.
