<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.uniformBooleanFunction_toMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform law on Boolean functions

**Claim.** For every $n$, the probability measure of a uniformly chosen Boolean function from the cube to $\{\pm1\}$ is the product, over all inputs, of the uniform probability measure on $\{\pm1\}$.

**Proof.** It suffices to compare the two measures on singleton sets, since the underlying function space is finite. Fix a function $f$. Under the uniform law on all functions, its probability is the reciprocal of the number of such functions. The function space consists of one independent sign choice for each cube input, so its cardinality is the number of signs raised to the number of inputs. On the product side, the singleton probability is the product of the uniform sign probabilities at each input, also the reciprocal of that same power. Every function takes only the two possible sign values, so these coordinate probabilities apply throughout. The singleton masses agree for every $f$, and thus the measures agree.
