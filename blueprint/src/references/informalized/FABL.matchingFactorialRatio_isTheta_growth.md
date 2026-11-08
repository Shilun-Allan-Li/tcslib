<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingFactorialRatio_isTheta_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial ratio growth order

**Claim.** For fixed $r>0$, the factorial ratio and $k^{(1-r)/2}$ have the same order of growth up to positive constant factors as $k$ tends to infinity.

**Proof.** The factorial ratio is asymptotic to the matching Stirling core, so the two have the same asymptotic growth order. The matching Stirling core has the same growth order as $k^{(1-r)/2}$. Transitivity of this comparison gives the asserted growth order for the factorial ratio.

**Key facts.** `FABL.matchingFactorialRatio_isEquivalent_core`, `FABL.matchingStirlingCore_isTheta_growth`.
