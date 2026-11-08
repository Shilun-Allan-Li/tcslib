<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PromiseKarpReducible.hasPolytimeDistinguisher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinguisher transfer under reduction

**Claim.** If a source promise problem reduces to a target promise problem by a polynomial-time map preserving promised yes- and no-instances, and the target has a polynomial-time distinguisher, then the source has a polynomial-time distinguisher.

**Proof.** Choose a polynomial-time reduction from the source to the target and a polynomial-time decision map distinguishing the target's promised cases. Compose the decision map with the reduction. A promised yes-instance of the source maps to a promised yes-instance of the target, so the target distinguisher outputs true there. Likewise, a promised no-instance maps to a promised no-instance, so the distinguisher outputs false. The composition is polynomial-time, and therefore distinguishes the source.
