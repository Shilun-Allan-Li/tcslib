<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformProbability_ne_eq_relativeHammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative Hamming distance as probability

**Claim.** For functions on a finite nonempty domain, the probability that their values differ equals their Hamming distance divided by the domain size.

**Proof.** By definition, the uniform probability is the average of the indicator of the event $f(x)\ne g(x)$. On a finite uniform space this average is the number of inputs satisfying that event divided by $|\Omega|$. That number is the Hamming distance, so the average is exactly the relative Hamming distance.
