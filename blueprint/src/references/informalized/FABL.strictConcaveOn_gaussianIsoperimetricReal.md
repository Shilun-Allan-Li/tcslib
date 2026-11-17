<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.strictConcaveOn_gaussianIsoperimetricReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict concavity of the Gaussian profile

**Claim.** The real-valued Gaussian isoperimetric profile is strictly concave on $[0,1]$.

**Proof.** The interval $[0,1]$ is convex, and the profile is continuous there (\(`FABL.continuousOn_gaussianIsoperimetricReal`\)). On the interior $(0,1)$, its second derivative is $-1$ divided by the profile value (\(`FABL.gaussianIsoperimetric_second_derivative`\)). The profile is positive on that interval (\(`FABL.gaussianIsoperimetricReal_pos`\)), so this second derivative is strictly negative throughout the interior. The criterion that a continuous function on a convex interval with strictly negative second derivative in its interior is strictly concave therefore applies.

**Key facts.** `FABL.continuousOn_gaussianIsoperimetricReal`, `FABL.gaussianIsoperimetric_second_derivative`, `FABL.gaussianIsoperimetricReal_pos`.
