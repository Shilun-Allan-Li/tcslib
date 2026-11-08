<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeRuntimeLedger_mul_treeCallCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree-Scaled Runtime Ledger Bounds

**Claim.** Multiplying the node's Fourier scan and polynomial learner runtime bounds by the tree call count preserves both bounds, with their right sides multiplied by the same count.

**Proof.** The node runtime ledger gives the unscaled Fourier scan inequality and the unscaled polynomial work inequality. For the Fourier inequality, the tree call count is nonnegative, so multiplication preserves the order in the rational numbers. For the polynomial inequality, both sides are natural numbers, and multiplication by the natural tree call count likewise preserves order. Rewriting the runtime envelopes by their definitions gives the two claimed bounds.

**Key facts.** `FABL.lowDegreeJuntaNodeRuntimeLedger`.
