<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaTreePerCallFailure_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Per-call failure parameter

**Claim.** For a nonnegative depth $k$ and an admissible learning parameter $\tau$, the per-call failure parameter is $\tau$ divided by the junta tree call count at depth $k$.

**Proof.** By definition, the per-call failure parameter is the subtype whose underlying rational value is the failure parameter divided by the call count. Taking its underlying value gives the claimed equality directly.
