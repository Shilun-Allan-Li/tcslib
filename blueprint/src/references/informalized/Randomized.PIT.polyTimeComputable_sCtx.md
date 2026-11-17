<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sCtx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Context Projection

**Claim.** The transformation sending each finite bit string $D$ to $\mathrm{sCtx}(D)$ is polynomial-time computable.

**Proof.** By definition, $\mathrm{sCtx}$ is the total first-component projection on the input string. That projection is polynomial-time computable (`polyTimeComputable_pairFstD`), which proves the claim.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`.
