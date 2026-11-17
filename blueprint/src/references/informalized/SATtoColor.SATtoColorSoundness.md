<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean :: SATtoColor.SATtoColorSoundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Coloring Reduction

**Claim.** If the reduction graph of a 3-SAT instance has a proper three-coloring, then the instance has a satisfying Boolean assignment.

**Proof.** Fix a proper coloring. The three palette vertices are pairwise adjacent, so they receive distinct colors. Define an assignment by setting a variable true exactly when its positive-literal vertex has the palette-1 color. The positive- and negative-literal vertices of each variable are adjacent, so the negative-literal vertex has the opposite truth value: a literal that is false cannot have color 1. Now fix any clause and suppose all three of its literals were false. Its three literal vertices would therefore avoid colors 0 and 1, since each is adjacent to palette 0 and, by falsity, differs from palette 1. Hence all three would have color 2. The clause gadget's vertex numbered 5 is adjacent to palette vertices 0 and 2, so it must have color 1. The gadget vertices 0, 1, 2, 3, and 4, together with their prescribed edges to the literal vertices and to one another, cannot then be colored with the remaining colors while keeping each edge properly colored: the finite list of inequalities from these edges forces a contradiction. Thus at least one literal of the clause is true. This holds for every clause, so the extracted assignment satisfies the instance.
