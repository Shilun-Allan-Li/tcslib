<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Key Transformation

**Claim.** The transformation sending each finite bit string $D$ to $\mathrm{sK}(D)$ is polynomial-time computable.

**Proof.** First extract the context projection $\mathrm{sCtx}(D)$, then apply the total second-component projection followed by the total first-component projection; this composite is polynomial-time computable by closure under composition (`PolyTimeComputable.comp`, using `polyTimeComputable_sCtx` and `polyTimeComputable_slot2`). Pair its result with the constant string $[\mathrm{true}]$. Pair encoding is polynomial-time computable when both component transformations are (`PolyTimeComputable.pairEncode`), and the constant component is polynomial-time computable (`polyTimeComputable_const`). Applying binary addition to this encoded pair preserves polynomial-time computability by composition with the polynomial-time addition transformation (`polyTimeComputable_add`). The resulting composite is $\mathrm{sK}$.

**Key facts.** `Randomized.PIT.polyTimeComputable_sCtx`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.PolyTimeComputable.comp`.
