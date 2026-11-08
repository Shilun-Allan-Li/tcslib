<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.family_eval_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-family evaluation and language membership

**Claim.** For a Boolean string $q$ of length $N$, evaluating the family circuit for length $N$ on the input whose $i$th bit is $q_i$ (with false used out of range) yields true exactly when $q$ belongs to the family's language.

**Proof.** Use the hypothesis that $q$ has length $N$ to replace $N$ by $q.length$. For each index $i$ in the finite input range, the value $q.getD(i,false)$ is then exactly the $i$th entry of the length-indexed list $q.get$. Hence the function supplied to the circuit agrees pointwise with $q.get$. The language-membership characterization (`mem_language_iff`) identifies acceptance by the length-$q.length$ circuit on $q.get$ with membership of $q$ in the language. Replacing the input by the pointwise equal function proves the equivalence.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
