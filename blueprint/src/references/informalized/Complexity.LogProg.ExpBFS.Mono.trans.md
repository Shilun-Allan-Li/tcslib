<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.Mono.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Boolean Implication

**Claim.** If truth of $M$ implies truth of $M'$, and truth of $M'$ implies truth of $M''$, then truth of $M$ implies truth of $M''$.

**Proof.** Fix an integer $z$ at which $M$ is true. The first implication gives that $M'$ is true at $z$, and the second then gives that $M''$ is true there. Thus truth of $M$ implies truth of $M''$ at every integer.
