<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_sI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Input Projection

**Claim.** The transformation sending each finite bit string $D$ to $\mathrm{sI}(D)$ is polynomial-time computable.

**Proof.** The third nested slot projection $D\mapsto \mathrm{pairSndD}(\mathrm{pairSndD}(D))$ is polynomial-time computable (`polyTimeComputable_slot3`). Apply the polynomial-time total first-component projection to its output (`polyTimeComputable_pairFstD`). Closure under composition (`PolyTimeComputable.comp`) gives the claimed transformation, which is exactly $\mathrm{sI}$.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`.
