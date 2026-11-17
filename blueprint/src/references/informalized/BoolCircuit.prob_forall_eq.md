<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_forall_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Specified Boolean Function

**Claim.** For a uniformly chosen Boolean function on $n$ inputs, the probability of agreeing everywhere with any specified Boolean function $g$ is $2^{-2^n}$.

**Proof.** The event that a function $f$ agrees with $g$ at every input is exactly the singleton event $\{g\}$: pointwise equality implies equality of functions, and equality of functions implies pointwise equality. The uniform distribution assigns each element of its finite function space the reciprocal of the space's cardinality. There are $2^{2^n}$ Boolean functions on $n$ inputs (`BoolCircuit.card_boolFun`), since there are $2^n$ inputs and two independent choices of output at each. Hence the singleton has probability $1/2^{2^n}=2^{-2^n}$.

**Key facts.** `BoolCircuit.card_boolFun`.
