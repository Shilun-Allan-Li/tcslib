<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingImprovementConstant_isTheta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improvement constant growth order

**Claim.** For fixed $r>0$, the improvement constant has the same growth order, up to positive constant factors, as $k^{-1/4+1/(4r)}$ as $k$ tends to infinity.

**Proof.** The factorial ratio and matching core growth are eventually nonnegative, so taking both to the power $1/(2r)$ preserves their asymptotic comparison. The factorial ratio is of the same growth order as the matching core growth. The improvement constant is exactly the corresponding power of the factorial ratio, while the same power of the matching core growth equals the matching improvement growth by the power identity. Substituting these two equalities into the powered comparison yields the claimed growth order.

**Key facts.** `FABL.matchingFactorialRatio_isTheta_growth`, `FABL.matchingImprovementConstant_eq_rpow_factorialRatio`, `FABL.matchingCoreGrowth_rpow_eq_improvementGrowth`.
