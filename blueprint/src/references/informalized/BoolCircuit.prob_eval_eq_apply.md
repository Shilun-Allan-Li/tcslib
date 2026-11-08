<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_eval_eq_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Input Agreement Probability

**Claim.** For a directed acyclic circuit $C$ with $n$ Boolean inputs and any input $x$, a uniformly chosen Boolean function agrees with $C$ at $x$ with probability $1/2$.

**Proof.** At the fixed input $x$, the circuit has a definite Boolean value $g(x)=C.eval(x)$. For any specified Boolean function $g$ and input $x$, a uniformly chosen Boolean function agrees with $g$ at $x$ with probability $1/2$ (`BoolCircuit.prob_apply_eq`). Taking $g$ to be the function computed by $C$ proves the assertion.

**Key facts.** `BoolCircuit.prob_apply_eq`.
