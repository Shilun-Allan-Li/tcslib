<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.affineSubspacePCPPSystem_isPCPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The affine subspace system is a PCPP

**Claim.** The constructed system is a PCPP for the affine-subspace property with rejection rate $1/8$.

**Proof.** Use the criterion that completeness together with the stated high-acceptance-to-closeness implication yields a PCPP (`FABL.isPCPP_of_exists_close_of_acceptanceProbability_ge`). The rate $1/8$ is positive. For completeness, each word in the property has an encoded truth-table proof for its character, and the system accepts that proof with probability $1$ (`FABL.affineSubspacePCPPSystem_complete`). For soundness, the high-acceptance theorem (`FABL.affineSubspacePCPPSystem_close_of_acceptanceProbability_ge`) says that acceptance at least $1-\frac18\epsilon$ produces a property word within distance $\epsilon$. If the input is farther than $\epsilon$ from every property word, this implication rules out that acceptance bound; hence rejection is strictly greater than $\frac18\epsilon$, as required.

**Key facts.** `FABL.isPCPP_of_exists_close_of_acceptanceProbability_ge`, `FABL.affineSubspacePCPPSystem_complete`, `FABL.affineSubspacePCPPSystem_close_of_acceptanceProbability_ge`.
