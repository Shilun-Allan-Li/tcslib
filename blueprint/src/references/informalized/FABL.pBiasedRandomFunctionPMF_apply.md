<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.pBiasedRandomFunctionPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point probabilities of a biased random function

**Claim.** Under the product probability law in which each function value is an independent bit with true probability $p$, the probability of obtaining a particular function is the product over all inputs of the probability that the corresponding bit equals its specified value.

**Proof.** The random-function law is defined as the independent product of the single-bit laws. By the defining point-mass formula for an independent product, the probability assigned to a function $f$ is the product of the probabilities assigned by the individual bit laws to $f(x)$, over every input $x$. This is exactly the stated formula.
