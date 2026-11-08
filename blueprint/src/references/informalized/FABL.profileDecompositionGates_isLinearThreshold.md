<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.profileDecompositionGates_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of Decomposition Gates

**Claim.** Every gate in the family indexed by pairs of a coordinate and a gate type is a linear threshold function.

**Proof.** Fix the index $j$ and decode it as a coordinate $i$ together with one of the two gate types. The definition of the family then gives two cases. If the gate is the main gate at $i$, it is a linear threshold function by the result for profile main gates (\texttt{FABL.profileMainGate_isLinearThreshold}). If it is the correction gate, the corresponding result for profile correction gates applies (\texttt{FABL.profileCorrectionGate_isLinearThreshold}). Thus either possible gate is a linear threshold function.

**Key facts.** `FABL.profileMainGate_isLinearThreshold`, `FABL.profileCorrectionGate_isLinearThreshold`.
