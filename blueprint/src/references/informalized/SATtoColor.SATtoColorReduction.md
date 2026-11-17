<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean :: SATtoColor.SATtoColorReduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Coloring Reduction

**Claim.** A 3-SAT instance is satisfiable if and only if its reduction graph is 3-colorable.

**Proof.** Apply the completeness result to obtain a proper three-coloring from any satisfying assignment. Conversely, apply the soundness result to recover a satisfying assignment from any proper three-coloring. These two implications are exactly the two directions of the stated equivalence.

**Key facts.** `SATtoColor.SATtoColorCompleteness`, `SATtoColor.SATtoColorSoundness`.
