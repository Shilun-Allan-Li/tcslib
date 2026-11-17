<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.inBPPWeak_polyTimeModel_iff_inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak and Standard BPP

**Claim.** For every natural number $c$ and language $L$, $L$ is in weak BPP with advantage parameter $c$ in the polynomial-time model if and only if $L$ is in standard BPP in that model.

**Proof.** The general weak-to-standard equivalence says that, in any verifier model closed under majority, a verifier with the specified inverse-polynomial advantage can be amplified to meet the standard BPP error bound; conversely, standard BPP already supplies at least the required weak success probability. The polynomial-time model is closed under majority, so applying that equivalence to this model gives the result.

**Key facts.** `Randomized.inBPPWeak_iff_inBPP`, `Randomized.polyTimeModel_closedUnderMajority`.
