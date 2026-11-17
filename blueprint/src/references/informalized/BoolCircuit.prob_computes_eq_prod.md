<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_computes_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for Circuit Agreement

**Claim.** For a directed acyclic circuit $C$ with $n$ Boolean inputs, the probability that a uniformly chosen Boolean function agrees with $C$ on every input is the product, over all inputs $x$, of the probability that it agrees with $C$ at $x$.

**Proof.** There are $2^n$ inputs. The probability of matching the circuit at any one specified input is $1/2$, by the single-input agreement result (`BoolCircuit.prob_eval_eq_apply`). The probability of matching it at every input is $2^{-2^n}$, by the all-input agreement result (`BoolCircuit.prob_computes`). Thus the product of the single-input probabilities is $(1/2)^{2^n}=2^{-2^n}$, which equals the probability of matching everywhere. These evaluations of the finite product are precisely the simplifications in the proof.

**Key facts.** `BoolCircuit.prob_eval_eq_apply`, `BoolCircuit.prob_computes`.
