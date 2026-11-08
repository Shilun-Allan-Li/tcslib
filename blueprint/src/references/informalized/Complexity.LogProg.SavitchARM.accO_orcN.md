<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean :: Complexity.LogProg.SavitchARM.accO_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Checker Characterization

**Claim.** The acceptance checker returns true on the nested encoding of $x$, $v$, and $s$ exactly when that word belongs to the language of accepting configurations.

**Proof.** By definition, the checker `orcN` at index $2$ is the indicator of the accepting-configuration language. The indicator equals the decision of membership (`Complexity.LogProg.indicator_eq_decide`), so its value on the specified word is true exactly when that word belongs to `Codec.acceptLang N`. Unfolding the definition of `AccO` identifies its assertion with that same Boolean value, proving the equivalence.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
