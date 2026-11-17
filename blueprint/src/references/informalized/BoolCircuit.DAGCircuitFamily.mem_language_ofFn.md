<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuitFamily.mem_language_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance of a finite assignment

**Claim.** For a Boolean assignment $v$ to $m$ positions, the word whose bits are given by $v$ belongs to the language of $F$ exactly when the circuit of $F$ for length-$m$ inputs evaluates to true on $v$.

**Proof.** Apply the language-membership characterization to the word formed from $v$: membership is equivalent to the circuit at the word's length evaluating on the word's indexed bits. The canonical identification of a length-$m$ word with its length and its assignment identifies this word with the pair $(m,v)$. Hence the condition is exactly that the length-$m$ circuit evaluates to true on $v$ (DAGCircuitFamily.mem_language_iff).

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
