<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_eq_toReal_iidBernoulli -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability as an iid Bernoulli Measure

**Claim.** For $0\le p\le1$, the biased probability of an event on length-$m$ Boolean words equals the probability, under the product measure of $m$ independent Bernoulli($p$) bits, that the associated word satisfies the event.

**Proof.** View the event as a subset of the finite space of Boolean vectors of length $m$. Since that space is finite, its measure is the sum of the singleton measures over vectors in the event. Under the product measure, the singleton measure of a vector is the product of its coordinate probabilities; a true coordinate contributes $p$, and a false coordinate contributes $1-p$. On the other hand, the finite-sum formula for biased probability (`Randomized.biasedProb_eq_sum`) expresses it as a sum over all vectors, retaining exactly the event vectors and assigning them this same product of coordinate weights. The singleton-sum expression for the measure and the biased-probability sum therefore agree, including after converting the measure to a real number.

**Key facts.** `Randomized.biasedProb_eq_sum`.
