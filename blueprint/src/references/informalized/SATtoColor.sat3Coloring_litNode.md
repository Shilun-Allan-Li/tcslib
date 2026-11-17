<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean :: SATtoColor.sat3Coloring_litNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Color of a Literal Vertex

**Claim.** Under the assignment-induced coloring, a literal vertex has color 1 if its literal is satisfied and color 2 otherwise.

**Proof.** For a positive literal, the coloring assigns color 1 when its variable is true and color 2 when false, exactly as the satisfaction rule requires. For a negative literal, the coloring assigns color 2 when its variable is true and color 1 when false; these are precisely the cases in which the negated literal is false or true, respectively.
