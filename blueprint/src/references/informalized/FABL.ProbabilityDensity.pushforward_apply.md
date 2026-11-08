<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensityPushforward.lean :: FABL.ProbabilityDensity.pushforward_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise formula for a pushforward density

**Claim.** At a point $z$, the pushforward density is the size of the target cube times the uniform mean over inputs $y$ of $\varphi(y)$ when $L(y)=z$, and of zero otherwise.

**Proof.** The pushforward density is defined pointwise by exactly this expression: the target cube's cardinality multiplies the uniform expectation over inputs of the indicated conditional value. The theorem follows by unfolding that definition.
