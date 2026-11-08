<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Circuit Agreement

**Claim.** For a directed acyclic circuit $C$ with $n$ Boolean inputs, a uniformly chosen Boolean function agrees with the function computed by $C$ on every input with probability $2^{-2^n}$.

**Proof.** The circuit computes a particular Boolean function $g$, namely $g(x)=C.eval(x)$. The probability that a uniformly chosen Boolean function agrees with $g$ at every input is $2^{-2^n}$, by the probability-of-a-specified-function result (`BoolCircuit.prob_forall_eq`). Applying that result to the circuit's computed function gives the claim.

**Key facts.** `BoolCircuit.prob_forall_eq`.
