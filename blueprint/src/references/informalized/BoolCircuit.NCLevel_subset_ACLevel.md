<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.NCLevel_subset_ACLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inclusion of Circuit Complexity Levels

**Claim.** For every natural number $i$, every Boolean language in the depth-$i$ class $\textsf{NC}$ also belongs to the depth-$i$ class $\textsf{AC}$.

**Proof.** Take a language in $\textsf{NC}^i$. By the fact that bounded fan-in circuits are also well-formed circuits, with the same size, depth, and accepted language (`Language.InNC.inAC`), this language belongs to $\textsf{AC}^i$. Thus $\textsf{NC}^i\subseteq\textsf{AC}^i$.

**Key facts.** `Language.InNC.inAC`.
