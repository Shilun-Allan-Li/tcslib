<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DecisionTreeHypotheses.lean :: FABL.DecisionTreeHypothesis.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Tree Encoding Round Trip

**Claim.** For every natural number $n$ and every decision tree with sign-valued leaves and coordinates in $\\{0,\\ldots,n-1\\}$, decoding its encoded bit list returns the original tree.

**Proof.** Encoding a tree takes its natural-number encoding and writes that number as a list of bits. Decoding first converts the bit list back to a natural number, then applies the standard decoder for the tree type. The bit-list conversion recovers the original natural number, and the decoder for an encodable object recovers the object that was encoded. Applying these two inverse properties to the given tree gives the result.
