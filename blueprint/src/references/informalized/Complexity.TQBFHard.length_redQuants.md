<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.length_redQuants -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the reduction quantifier list

**Claim.** The reduction quantifier list has length $3R^2+3R$, where $R$ is its width parameter.

**Proof.** Write $R$ for the reduction width. The list consists of three repeated blocks, each of length $R$, followed by the level quantifier list of width and depth both equal to $R$. The latter has length $3R\cdot R$ by the length formula for level quantifiers (Complexity.TQBFHard.length_levelQuants). Adding the four lengths gives $3R+3R^2$, which is the defined reduction measure.

**Key facts.** `Complexity.TQBFHard.length_levelQuants`.
