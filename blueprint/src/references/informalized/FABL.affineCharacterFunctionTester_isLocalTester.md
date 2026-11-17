<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineCharacterFunctionTester_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Character Tester Is Local

**Claim.** The three-query affine character tester accepts every sign-valued function that is a character with frequency in $a+V^\perp$ with probability $1$, and functions farther than $\varepsilon$ from every such character have rejection probability greater than $\varepsilon$ for $\varepsilon\in[0,1]$.

**Proof.** First use the local-testing theorem for perpendicular characters on $V^\perp$; it gives rate $1$ for the tester built from that subspace. Twisting both the tester and its tested functions by the character of frequency $a$ preserves this local-testing guarantee (FABL.isLocalTester_signTwist). The affine-character characterization identifies membership in the affine frequency class $a+V^\perp$ exactly with the twisted function being a perpendicular character for $V^\perp$ (FABL.isAffineFrequencyCharacter_iff_twist_isPerpendicularCharacter). Replacing the tester's property by this equivalent one yields the claimed guarantee (FABL.IsLocalTester.congr_property).

**Key facts.** `FABL.perpendicularCharacterFunctionTester_isLocalTester`, `FABL.isLocalTester_signTwist`, `FABL.isAffineFrequencyCharacter_iff_twist_isPerpendicularCharacter`, `FABL.IsLocalTester.congr_property`.
