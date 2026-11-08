<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineSubspacePCPPSystem_close_of_acceptanceProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness from high acceptance

**Claim.** If the affine subspace PCPP system accepts with probability at least $1-\frac18\epsilon$, then the input is within distance $\epsilon$ of a word in the affine-subspace property.

**Proof.** 1. The verifier uniformly mixes two testers. The component bound for a uniform mixture (`FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`) shows that each tester accepts with probability at least $1-\frac14\epsilon$. In particular, the affine-subspace proof tester meets this threshold.

2. Lifting the truth-table proof to the combined input-proof domain preserves its acceptance probability (`FABL.f₂TruthTableLiftTester_acceptanceProbability`). Thus the associated function on the Boolean cube is accepted by the affine-character tester with probability at least $1-\frac14\epsilon$. Apply the local tester soundness theorem (`FABL.IsLocalTester.close_of_acceptanceProbability_ge`), using that this character tester is a rate-one local tester (`FABL.affineCharacterFunctionTester_isLocalTester`). It yields a character indexed by some $\gamma$ in the affine-frequency property whose truth table is within distance $\epsilon/4$ of the proof function.

3. Decode $\gamma$ as a Boolean word $w_0$. Its membership in the affine-frequency property says exactly that $w_0$ belongs to the desired affine-subspace property. The coordinate-correction estimate (`FABL.affineCoordinateCorrectionProbability_ge`) implies that, for every coordinate, correction outputs the corresponding bit of $w_0$ with probability at least $1-2(\epsilon/4)\ge 1/2$, since $0\le\epsilon\le1$.

4. The consistency tester's rejection controls the distance from the input to $w_0$: the half-distance bound (`FABL.half_relativeHammingDist_le_affineConsistency_rejection`) gives $\frac12\operatorname{dist}(w,w_0)$ at most its rejection probability. Its acceptance is at least $1-\frac14\epsilon$, so its rejection is at most $\epsilon/4$. Consequently $\operatorname{dist}(w,w_0)\le\epsilon/2\le\epsilon$. This supplies a property word within the required distance.

**Key facts.** `FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`, `FABL.f₂TruthTableLiftTester_acceptanceProbability`, `FABL.affineCharacterFunctionTester_isLocalTester`, `FABL.IsLocalTester.close_of_acceptanceProbability_ge`, `FABL.affineCoordinateCorrectionProbability_ge`, `FABL.half_relativeHammingDist_le_affineConsistency_rejection`.
