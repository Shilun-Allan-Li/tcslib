<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/NAESATToColoring.lean :: NAEtoColor.NAEtoColorSoundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the NAE Coloring Reduction

**Claim.** If the reduction graph of a NAE-SAT instance $f$ is 3-colorable, then $f$ has a Boolean assignment under which every clause has values that are not all equal.

**Proof.** Let $\operatorname{col}$ be a proper coloring of the reduction graph, and write $g$ for the color of the ground vertex. Every variable vertex has a color different from $g$. Define the color representing true to be the successor of $g$ in the three-color cycle, and assign a variable true exactly when its vertex has that color. Thus variables assigned false avoid both $g$ and the true color, so they all have the unique remaining color.

Suppose, for contradiction, that some clause is not satisfied. Its three Boolean values must then be equal. If they are all true, the three variable vertices have the same color by the definition of the assignment. If they are all false, each avoids the ground color and the true color, so again their colors are equal.

Now consider the three gadget vertices for this clause. They form a triangle, so their colors are pairwise distinct. Each is also adjacent to the variable vertex in its corresponding clause position. Since all three variables have the same color, all three gadget vertices must avoid that one color. But three pairwise distinct colors cannot all be chosen from the other two colors. This contradiction shows that every clause is satisfied by the constructed assignment.
