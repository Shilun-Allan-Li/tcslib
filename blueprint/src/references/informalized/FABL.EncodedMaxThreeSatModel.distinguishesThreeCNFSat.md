<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.EncodedMaxThreeSatModel.distinguishesThreeCNFSat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinguishing Three-CNF Satisfiability

**Claim.** Under the stated validity, optimum, approximation, and threshold-test assumptions, the threshold test outputs true on satisfiable valid formula encodings and false on unsatisfiable valid formula encodings.

**Proof.** We verify the two promised cases. For a yes input, decode it. If decoding fails, the assumed satisfiability condition is impossible, so this case is vacuous. Otherwise, the encoding's canonicality property identifies the input with the encoding of its decoded formula. That formula is satisfiable, so the model's optimum is one. The threshold-approximation guarantee therefore gives an algorithm value at least one, and the threshold test outputs true. For a no input, decoding must likewise succeed. Canonicality and the model's optimum characterization imply that the optimum is not one; since it is at most one, it is strictly less than one. Every feasible solution has value at most the optimum, and the algorithm returns a feasible solution, so its value is strictly less than one. The threshold test consequently outputs false.
