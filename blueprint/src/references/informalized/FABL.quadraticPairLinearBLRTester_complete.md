<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairLinearBLRTester_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Linear Tester

**Claim.** For every vector γ, the linear tester accepts the function x ↦ γ·x with probability 1.

**Proof.** The acceptance probability of the quadratic-pair tester on this oracle reduces, by the acceptance-probability identity for the linear branch (quadraticPairLinearBLRTester_acceptanceProbability), to the acceptance probability of the ordinary BLR tester on x ↦ γ·x. The dot-product characterization of linear functions says that a function is linear exactly when it is a dot product with some fixed vector (isF₂Linear_iff_exists_dotProduct); here that vector is γ. The BLR completeness theorem (blrFunctionTester_complete) then gives acceptance probability 1.

**Key facts.** `FABL.quadraticPairLinearBLRTester_acceptanceProbability`, `FABL.isF₂Linear_iff_exists_dotProduct`, `FABL.blrFunctionTester_complete`.

**Caveat.** The supplied informal statement describes a PCPP construction, but the formal statement and proof establish only completeness of the linear branch tester.
