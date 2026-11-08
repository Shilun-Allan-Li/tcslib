<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.prob_computableDAG_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Bound for Small Circuits

**Claim.** The probability that a uniformly chosen Boolean function on $n$ inputs is computable by a circuit of size at most $S$ is at most the number of such functions times $2^{-2^n}$.

**Proof.** Since the set of computable functions is finite, enumerate it as a finite set $D$. Every function in the set agrees everywhere with one of the functions indexed by $D$ (namely itself). The probability in question is thus bounded by the probability that the random function agrees everywhere with at least one member of this finite family. The union bound for agreement with a finite family (BoolCircuit.prob_exists_eq_le) bounds that probability by $|D|\,2^{-2^n}$. Finally, $|D|$ is the cardinality of the set of computable functions, giving the claim.

**Key facts.** `BoolCircuit.prob_exists_eq_le`.
