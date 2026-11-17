<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.idxCircuit_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding an input-index circuit

**Claim.** For $j<n$, the Boolean-word encoding of the circuit with $n$ inputs, no gates, and output vertex $j$ is the word of $n$ true bits followed by false, two further false bits, and then $j$ true bits followed by false.

**Proof.** Unfold the circuit encoding. Its input-count field is `encodeNat n`, which is $n$ true bits followed by false. Since the gate list is empty, its list encoding is the singleton false marker. The output field is `encodeNat j`, namely $j$ true bits followed by false. Concatenating these fields gives exactly the stated word.
