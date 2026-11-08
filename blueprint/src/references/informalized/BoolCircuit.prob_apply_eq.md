<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_apply_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of One Matching Input

**Claim.** For Boolean functions chosen uniformly at random, the probability that the chosen function agrees with a fixed function $g$ at a fixed input $x$ is $1/2$.

**Proof.** Consider the involution that changes a function's value at $x$ to its Boolean negation and leaves all other values unchanged. It is its own inverse, and it exchanges functions satisfying $f(x)=g(x)$ with those that do not. Hence the two classes have equal cardinality and together partition all Boolean functions, so each class has half of the total. Under the uniform distribution, the probability of the first class is therefore $1/2$.
