<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInnerFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Tester Acceptance Identity

**Claim.** The inner tester's acceptance probability on the combined word $(w,p)$ equals the homogeneous quadratic PCPP verifier's acceptance probability on the extension proof and inner proof extracted from $p$.

**Proof.** The inner tester is obtained by reindexing the homogeneous quadratic verifier's query addresses into the combined input-proof address space. Acceptance probability is preserved under this reindexing, with the tested function composed with the address map (`reindexDomainFunctionTester_acceptanceProbability`). On an address from the extension-proof portion, the reindexed combined word returns the corresponding restriction of $p$; on an address from the inner-proof portion, it returns that portion's restriction. Thus the two tested functions agree at every address, giving the claimed identity.

**Key facts.** `FABL.reindexDomainFunctionTester_acceptanceProbability`.
