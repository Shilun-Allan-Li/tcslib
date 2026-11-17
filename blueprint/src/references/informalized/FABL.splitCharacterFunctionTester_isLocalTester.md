<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.splitCharacterFunctionTester_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The split character tester is local

**Claim.** The split character tester is a local tester for the perpendicular characters, with rejection rate one.

**Proof.** Use the criterion that completeness together with the implication from sufficiently high acceptance to closeness establishes a local tester (`isLocalTester_of_close_of_acceptanceProbability_ge`). The rate is positive. For completeness, convert a perpendicular character into a split character using the equivalence between these two descriptions (`isSplitCharacter_iff_isPerpendicularCharacter`), then apply perfect completeness (`splitCharacterFunctionTester_complete`).

For the closeness implication, the Fourier coefficient selection result supplies some frequency $\gamma$ whose coefficient is at least the expected product of the coset average with the section-sign convolution (`exists_vectorFourierCoeff_ge_expect_mul_signConvolution`). The split correlation identity identifies that expected product with the tester correlation (`splitCharacterCorrelation_eq_expect_mul_convolution`). If acceptance is at least $1-\epsilon$, the acceptance-correlation formula then implies that the correlation is at least $1-2\epsilon$ (`splitCharacterFunctionTester_acceptanceProbability`). Thus the selected Fourier coefficient is also at least $1-2\epsilon$. The coefficient-distance identity says this coefficient equals one minus twice the distance from $f$ to the split character indexed by $\gamma$ (`BinarySubspaceSplit.vectorFourierCoeff_cosetAverage_eq_one_sub_two_distance`). Comparing the bounds yields distance at most $\epsilon$. This character belongs to the perpendicular-character property by the same equivalence, giving the required closeness and completing the criterion.

**Key facts.** `FABL.isLocalTester_of_close_of_acceptanceProbability_ge`, `FABL.splitCharacterFunctionTester_complete`, `FABL.isSplitCharacter_iff_isPerpendicularCharacter`, `FABL.exists_vectorFourierCoeff_ge_expect_mul_signConvolution`, `FABL.splitCharacterCorrelation_eq_expect_mul_convolution`, `FABL.splitCharacterFunctionTester_acceptanceProbability`, `FABL.BinarySubspaceSplit.vectorFourierCoeff_cosetAverage_eq_one_sub_two_distance`.
