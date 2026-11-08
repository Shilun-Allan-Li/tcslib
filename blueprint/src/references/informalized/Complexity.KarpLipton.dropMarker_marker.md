<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.dropMarker_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deleting a marker prefix

**Claim.** For every $k$ and bit string $p$, the marker-deletion transducer sends $1^k0p$ to $p$.

**Proof.** Unfold the transducer. For $k=0$, the initial state is the state that deletes the marker: on reading the first $0$, it changes to the state that copies the remaining input, while producing no output for that marker bit. The remaining string is therefore passed through unchanged; the copying-state identity is `transduce_drop_true`. For the induction step, write $1^{k+1}0p$ as an initial $1$ followed by $1^k0p$. In the initial state, reading a $1$ produces that bit and leaves the transducer in the marker-deleting state. The induction hypothesis then shows the rest is sent to $p$.

**Key facts.** `Complexity.KarpLipton.transduce_drop_true`.
