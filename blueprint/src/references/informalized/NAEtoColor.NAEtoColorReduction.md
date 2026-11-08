<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/NAESATToColoring.lean :: NAEtoColor.NAEtoColorReduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the NAE Coloring Reduction

**Claim.** For every NAE-SAT instance $f$, the instance is satisfiable if and only if its reduction graph is 3-colorable.

**Proof.** Apply the two directions of the reduction separately. Completeness ( `NAEtoColor.NAEtoColorCompleteness` ) shows that a satisfying assignment yields a 3-coloring of the reduction graph. Soundness ( `NAEtoColor.NAEtoColorSoundness` ) shows that any such coloring yields a satisfying assignment. Together these implications give the equivalence.

**Key facts.** `NAEtoColor.NAEtoColorCompleteness`, `NAEtoColor.NAEtoColorSoundness`.
