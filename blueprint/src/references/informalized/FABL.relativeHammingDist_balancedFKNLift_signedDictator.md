<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.relativeHammingDist_balancedFKNLift_signedDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Under the Balanced Lift

**Claim.** The relative Hamming distance from the balanced lift of $f$ to a signed dictator equals the distance from $f$ to the corresponding function obtained by evaluating that signed dictator after adjoining $+1$ as the first coordinate.

**Proof.** Rewrite both distances as probabilities of disagreement (`FABL.uniformProbability_ne_eq_relativeHammingDist`). The uniform expectation over the $(n+1)$-dimensional cube splits into the average of its two slices with first coordinate $+1$ and $-1$ (`FABL.expect_fin_cons`). On the $+1$ slice, the disagreement indicator is exactly that between $f$ and the stated projection, by the definitions. For the $-1$ slice, change variables by negating the remaining input; this is a bijection of the smaller cube. Under this change, the balanced lift at the negative slice is $-f(-x)$ (`FABL.balancedFKNLift_fin_cons_neg_one`), and the signed dictator there is the negative of its value on the corresponding positive slice (`FABL.signedDictator_fin_cons_neg_one`). Negating both signs preserves disagreement, so this slice has the same disagreement probability as the positive slice. The average of two equal probabilities is that common value, proving the identity.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.expect_fin_cons`, `FABL.balancedFKNLift_fin_cons_neg_one`, `FABL.signedDictator_fin_cons_neg_one`.
