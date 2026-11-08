<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.tableauCircuit_eval_of_decidesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Tableau Circuit

**Claim.** For every length-n Boolean input, the tableau circuit with time parameter $T(n)$ outputs the indicator of whether that input belongs to $L$.

**Proof.** The tableau circuit evaluation theorem identifies its output with the assertion that the machine emits true at some time $s<T(n)$ on the input represented by $x$ (Complexity.tableauCircuit_eval). The machine's decision hypothesis says that it halts by time $T(|y|)$ and outputs exactly the membership indicator for every input $y$. Applying the consequence that a deciding machine emits true at some time before its bound exactly when the input belongs to the language (Complexity.decide_emits_eq_indicator) to $y=\mathrm{List.ofFn}(x)$ gives the desired equality: this list has length $n$, so its time bound is $T(n)$.

**Key facts.** `Complexity.tableauCircuit_eval`, `Complexity.decide_emits_eq_indicator`.
