<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingCoreGrowth_rpow_eq_improvementGrowth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power identity for matching growth

**Claim.** For natural numbers $r,k$ with $r>0$, raising the matching core growth to the power $1/(2r)$ gives the matching improvement growth.

**Proof.** By the multiplication law for real powers with nonnegative base, the iterated power is $k^{((1-r)/2)(1/(2r))}$. Since $r>0$, the exponent simplifies by ordinary field arithmetic to $-1/4+1/(4r)$. This is precisely the defining exponent of the matching improvement growth.
