<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.shiftRun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Run Encodes Shifted Gates

**Claim.** For every natural number $m$ and finite gate list $g_s$, the shift run on the pairing of the unary string of length $m$ with the gate-list encoding returns the concatenation of the marker and encoding for each gate shifted by $m$, in order.

**Proof.** The run extracts the two components of its input pairing using the pairing-decoding identities (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`). Its number of iterations is sufficient to process every gate: the gate-list encoding has length strictly greater than the number of gates (`Randomized.AlgCircuit.length_encodeGates`), so the iteration count exceeds that list length. The iteration theorem for shift steps (`Randomized.PIT.iterate_shStep`) then identifies the resulting nested pair: the remaining gate marker is paired with the original output followed by the encodings of the shifted gates. Here the original output is empty. Extracting the output component gives precisely the stated concatenation.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.AlgCircuit.length_encodeGates`, `Randomized.PIT.iterate_shStep`.
