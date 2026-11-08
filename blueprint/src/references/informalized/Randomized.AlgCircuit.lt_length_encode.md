<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.lt_length_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit encoding length

**Claim.** If a circuit has $n$ input variables and $s$ gates, its Boolean encoding has length strictly greater than $n+s$.

**Proof.** The circuit encoding concatenates the encoding of $n$ with the encoding of its gate list. The encoding of $n$ has length $n+1$, while the gate-list encoding has length strictly greater than $s$ by `length_encodeGates`. Adding these lengths shows that the full encoding has length greater than $n+s$.

**Key facts.** `Randomized.AlgCircuit.length_encodeGates`.
