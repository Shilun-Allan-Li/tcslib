<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ParityBasis.lean :: FABL.integral_uniformPMF_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform integral equals expectation

**Claim.** On a finite nonempty set with measurable singletons, integrating a real-valued function against the measure induced by the uniform probability mass function gives its uniform expectation.

**Proof.** Express the integral with respect to the measure associated to a probability mass function as a sum over points, weighted by their probabilities. For the uniform mass function, every point has weight $1/|\Omega|$, so this is the sum of the function values divided by $|\Omega|$. The uniform expectation on a finite set is exactly this normalized sum. Reassociating the scalar factor and the finite sum gives the claimed equality.
