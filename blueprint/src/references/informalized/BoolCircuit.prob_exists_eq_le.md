<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_exists_eq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Family Agreement Bound

**Claim.** For a finite set $D$ of indices and a family $e$ of Boolean functions on $n$ inputs, the probability that a uniformly chosen Boolean function agrees everywhere with at least one $e(d)$, for $d\in D$, is at most $|D|2^{-2^n}$.

**Proof.** For each $d\in D$, let $A_d$ be the event that the chosen function agrees with $e(d)$ at every input. The event in question is the union of these events. The finite union bound for measures (`MeasureTheory.measure_biUnion_finset_le`) bounds its probability by the sum of the probabilities of the $A_d$. Each such probability is $2^{-2^n}$ by the specified-function agreement result (`BoolCircuit.prob_forall_eq`). Summing this same quantity over the $|D|$ indices gives $|D|2^{-2^n}$.

**Key facts.** `BoolCircuit.prob_forall_eq`.
