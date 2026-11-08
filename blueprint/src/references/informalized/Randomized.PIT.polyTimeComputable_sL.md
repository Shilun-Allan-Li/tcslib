<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Projection

**Claim.** The transformation sending each finite bit string $D$ to $\mathrm{sL}(D)$ is polynomial-time computable.

**Proof.** The total four-slot second-component projection is polynomial-time computable (`polyTimeComputable_slot4`). By the definition of $\mathrm{sL}$, this projection is exactly the desired transformation.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot4`.
