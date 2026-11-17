<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.uniformProbability_ne_zero_eq_hammingNorm_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero probability and Hamming norm

**Claim.** For a function from the binary cube to $\mathbb F_2$, the probability that it is nonzero equals its Hamming norm divided by $2^n$.

**Proof.** Apply the probability–relative-Hamming-distance identity (`FABL.uniformProbability_ne_eq_relativeHammingDist`) to $f$ and the zero function. The event that their values differ is exactly the event $f(x)\ne0$, and the Hamming distance from $f$ to zero is the number of inputs where $f$ is nonzero, namely its Hamming norm. The binary cube has $2^n$ elements, so its relative Hamming distance is the Hamming norm divided by $2^n$.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`.
