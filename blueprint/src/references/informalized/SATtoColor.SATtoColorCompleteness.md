<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean :: SATtoColor.SATtoColorCompleteness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Coloring Reduction

**Claim.** If a 3-SAT instance is satisfied by a Boolean assignment, then its reduction graph has a proper coloring with three colors.

**Proof.** Take a satisfying assignment and use the coloring induced by it: the palette vertices receive their designated colors, each literal vertex receives color 1 when its literal is true and color 2 otherwise, and the six vertices of each clause gadget receive the colors prescribed by the gadget rule. The literal-node coloring fact (`sat3Coloring_litNode`) identifies the color of each literal vertex with its truth value: it is 1 exactly when the literal is satisfied. To check that the coloring is proper, consider any edge, whose defining relation is symmetric up to reversing its endpoints. For palette-to-palette edges, the endpoint colors differ by construction. A literal vertex adjacent to palette color 0 has color 1 or 2, and opposite literal vertices for the same variable receive different colors. The remaining possible edges join a clause gadget to a palette vertex, a literal vertex, or another vertex of that same gadget. Substituting the prescribed gadget colors and considering the truth values of the clause's three literals verifies that each such pair has distinct colors. In particular, the gadget's required coloring is compatible with its literal attachments because the clause is satisfied. Thus every edge has differently colored endpoints, giving a proper three-coloring.

**Key facts.** `SATtoColor.sat3Coloring_litNode`.
