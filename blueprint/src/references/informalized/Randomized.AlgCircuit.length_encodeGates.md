<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.length_encodeGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding length exceeds gate count

**Claim.** For every finite list $gs$ of algebraic gates, the number of gates in $gs$ is strictly less than the length of its Boolean encoding.

**Proof.** Proceed by induction on $gs$. For the empty list, its encoding is the one-bit list `[false]`, so its length is strictly greater than zero. For a nonempty list $g :: gs$, the encoding adds an initial marker and the encoding of $g$ before the encoding of the tail. In particular, its length exceeds the tail encoding’s length by more than one, so the induction hypothesis that the tail encoding is longer than the tail’s gate list yields the desired strict inequality.
