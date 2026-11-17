<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.profileCorrectionGate_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the Profile Correction Gate

**Claim.** For any sign sequence and coordinate index, the profile correction gate is a linear threshold function on the sign cube.

**Proof.** Split according to whether the two consecutive signs $a(i+1)$ and $a(i)$ agree. If they agree, the gate is the constant function with value $-1$; if they differ, it is the constant function with value $a(i+1)$. Every constant sign-valued gate is a linear threshold function (FABL.constantThresholdGate_isLinearThreshold), so the gate is a linear threshold function in either case.

**Key facts.** `FABL.constantThresholdGate_isLinearThreshold`.
