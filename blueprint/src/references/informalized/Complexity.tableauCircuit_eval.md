<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.tableauCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Tableau Circuit Computes Acceptance

**Claim.** For an oblivious finite-state Turing machine over the binary alphabet, the tableau circuit with parameters $n,T$ outputs true on an input $x$ of length $n$ exactly when the machine emits $1$ at some time $s<T$.

**Proof.** Apply the tableau-gates evaluation theorem (`Complexity.tableauGates_values`) to the input list obtained from $x$, whose length is $n$, and to the construction through time $T+1$. Its acceptance-tracking conclusion says that the value at the acceptance vertex for time $T$ is the tableau acceptance predicate at time $T$. The output of the tableau circuit is exactly this vertex, so its evaluation equals that predicate. By definition, the predicate is true precisely when there is an emission of $1$ at some time strictly below $T$.

**Key facts.** `Complexity.tableauGates_values`.
