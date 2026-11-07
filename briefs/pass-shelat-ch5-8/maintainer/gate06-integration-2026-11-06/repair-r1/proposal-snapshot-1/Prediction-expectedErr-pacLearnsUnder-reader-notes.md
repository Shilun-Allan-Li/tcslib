# PAC Prediction: expected-error predicate reader proposal

One unapplied existing-proof repair for `expectedErr_le_of_pacLearnsUnder` in `TCSlib/LearningTheory/PAC/Prediction.lean` (frozen source 159–175).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `9c38e4c7181dac13237b699b2f0b40121c7cd7f3b029560189275b5bba11291a`.
- Proposed full source SHA256, memory only: `3b7381e8a55c0db86a3efc9bcd83ca4750f9e724bdfb50e9166b9ef7e6ff916a`.
- Patch SHA256: `d3e59f48faf5e38056ebcde8961a69514f4453d26df33f73378b44c63a7d5739`.

The mutable library file was not used as the patch base or edited.

## Observed diagnostics and root

The valid V3 seal 051 reports source 170/probe 220 (`h` is not a function) and source 162/probe 212 (the remaining expected-error bound is unsolved). Log SHA256 is `cfc07154b67aeca571413a309bcabc557765a191067fa4a6f186e36f9f3cba74`. The generic result records exit 1, two source diagnostics, unchanged probe SHA256 `944df0192479051dbb29e2066f48715b9522a546179b7f7d2fe9b69e204766a9`, and no fresh object.

The proof applies foreign sealed `PACLearnsUnder` directly to concept index `i`. Read the predicate through `(pacLearnsUnder_iff (FinDist.uniform X) C m L ε δ).mp h` first, then apply that pointwise theorem to `i`. The existing public contract in `LearningTheory/PAC/Defs.lean:173` states exactly:

```lean
PACLearnsUnder D C m L ε δ ↔ ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε
```

The unsolved expectation bound is consistent with the missing pointwise confidence bound; no independent root appears in the recorded residual goal. This diagnosis remains a static source assessment, not a checked repair result.

## Other reads in the same proof

The proof already reads `expectedErr` and `trialDist` through their owner equations; the distribution expectation through `FinDist.expect_prod`, `expect_le_expect`, and `expect_const`; the bounded-error estimate through `FinDist.expect_le_add_of_le_one`; `accuracyProb` through `accuracyProb_eq`; and the complement event through `FinDist.probTrue_not`. The concluding `dsimp only` reduces the displayed lambda applications and projections, while `linarith` combines the public inequalities. No missing owner reader, helper definition, new tactic block, or additional hypothesis is needed.

The theorem header, nonnegative accuracy premise, learning notion, sample law, data/algorithms, proof sketch, and admission census are unchanged. Static comparison confines the diff to one line in this one existing proof and preserves every byte outside it.

Only this patch and these notes were saved under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The proposal remains uncompiled and needs root's native/sealed verification.

**Ready to run**
