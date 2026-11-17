<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.indicator_indexLang_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator on an Encoded Index Word

**Claim.** For every predicate $p$, bit string $u$, and natural number $v$, the indicator of the indexed language evaluated at $\operatorname{pairEncode}(u,\operatorname{bits}(v))$ is the Boolean decision of whether $p(u,v)$ holds.

**Proof.** The indicator of a set at a point equals the Boolean decision of membership in that set (`LogProg.indicator_eq_decide`). Membership of the encoded word $\operatorname{pairEncode}(u,\operatorname{bits}(v))$ in the indexed language is equivalent to $p(u,v)$ (`pairEncode_mem_indexLang`). Substituting this equivalence into the indicator identity gives exactly the stated Boolean decision.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Complexity.pairEncode_mem_indexLang`.
