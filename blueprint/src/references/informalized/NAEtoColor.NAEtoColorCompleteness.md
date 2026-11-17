<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/NAESATToColoring.lean :: NAEtoColor.NAEtoColorCompleteness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Completeness of the NAE-SAT coloring reduction

**Claim.** If a NAE-SAT instance $f$ has a satisfying Boolean assignment, then its reduction graph admits a proper coloring with three colors.

**Proof.** Choose a satisfying assignment and use the reduction’s prescribed coloring: the ground vertex receives the neutral color, each variable vertex receives the color determined by its assigned Boolean value, and the three vertices in each clause gadget receive their colors according to the clause gadget rule. It remains to show that endpoints of every edge receive different colors. Because adjacency is defined by an edge relation in one of the two orientations, it suffices to check that any pair related by the directed edge relation has different colors; reversing the orientation preserves inequality.

The ground vertex is adjacent to variable vertices, and its neutral color differs from either color assigned to a variable. The ground vertex has no edge to a clause vertex, and there are no edges between two variable vertices. For a variable–clause edge, the edge relation says that the variable is the one named at the clause position corresponding to that clause vertex. Substituting that position into the gadget’s coloring rule shows that the two colors differ, for either Boolean value of each variable.

Finally, consider two clause vertices joined by an edge. They belong to the same clause, their indices are distinct, and that clause occurs in $f$. Since the assignment satisfies $f$, at least two of the clause’s three variables have different Boolean values. This guarantees that the gadget coloring assigns distinct colors to every pair of its differently indexed vertices. Thus every edge has differently colored endpoints, so the prescribed coloring is proper and the reduction graph is 3-colorable.

**Caveat.** The proof source uses the definition of `naeColoring` and the clause gadget coloring rule `clauseNodeColor`, but neither definition is included in the payload. The variable–clause and clause–clause color checks therefore cannot be independently spelled out from the supplied statements alone.
