<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean :: Complexity.LogProg.SavitchARM.initO_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial-Code Oracle Characterization

**Claim.** The initial-code oracle accepts the encoding of $x$, the binary word for $u$, and the binary word for $s$ exactly when that encoding belongs to the language of valid initial configuration codes for $N$.

**Proof.** By definition, the initial-code oracle is the indicator function of the initial-code language at index $1$. The indicator-to-membership identity (`Complexity.LogProg.indicator_eq_decide`) identifies its Boolean value with the decision that the encoded word belongs to that language. Unfolding the initial-oracle notation and the oracle's language selection yields the claimed equivalence.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
