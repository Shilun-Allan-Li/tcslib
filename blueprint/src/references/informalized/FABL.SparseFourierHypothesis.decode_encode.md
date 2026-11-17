<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.SparseFourierHypothesis.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding and decoding are inverse

**Claim.** For every sparse Fourier hypothesis, decoding its encoded bit list returns the original hypothesis.

**Proof.** The encoding stores the hypothesis using the natural number assigned by `Encodable.encode`, then takes that number’s binary bit list. The decoder interprets the list back as a natural number and applies `Encodable.decode`. Interpreting a natural number’s bit list recovers that number, and decoding an encoded object recovers the object; applying these two round-trip facts in succession gives the result.
