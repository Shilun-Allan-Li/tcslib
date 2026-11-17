<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Number Projection

**Claim.** The transformation sending each finite bit string $D$ to $\mathrm{sN}(D)$ is polynomial-time computable.

**Proof.** The context projection $\mathrm{sCtx}$ is polynomial-time computable. Applying the total first-component projection to its output is also polynomial-time computable (`polyTimeComputable_pairFstD`); closure under composition (`PolyTimeComputable.comp`) therefore proves that $\mathrm{sN}$ is polynomial-time computable.

**Key facts.** `Randomized.PIT.polyTimeComputable_sCtx`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
