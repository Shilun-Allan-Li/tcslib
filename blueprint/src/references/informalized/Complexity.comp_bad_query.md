<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_bad_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Malformed Queries Are Rejected

**Claim.** If $h$ is not the encoding of any bit string paired with a binary natural number, then the computational-language indicator evaluates to false at $h$, in either mode.

**Proof.** Suppose instead that the indicator at $h$ were true. The indicator agrees with the Boolean decision of membership (the indicator-to-decision identity, `Complexity.LogProg.indicator_eq_decide`), so $h$ would belong to the computational language. By the definition of that language, membership supplies bit strings $z$ and a natural number $p$ with $h=\operatorname{pairEncode}(z,\operatorname{bin}(p))$. This contradicts the hypothesis that no such encoding exists. Thus the indicator is false.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
