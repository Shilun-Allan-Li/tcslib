<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedCorrelatedPairPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint point mass formula

**Claim.** The probability assigned to the pair $(x,y)$ by the joint law is the product of the uniform probability of $x$ and the conditional noise probability of $y$ given $x$.

**Proof.** By definition, the joint law first samples a point $z$ from the uniform distribution and then maps the conditional draw to $(z,w)$. Its mass at $(x,y)$ is therefore a finite sum over $z$ of the uniform mass at $z$ times the conditional mass that the mapped pair equals $(x,y)$. The latter is zero unless $z=x$; the sum over $z$ thus reduces to the term at $x$. For that term, the mapped pair equals $(x,y)$ precisely when the conditional draw is $y$, leaving the product of the two stated probabilities.
