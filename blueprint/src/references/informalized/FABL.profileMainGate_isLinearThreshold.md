<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.profileMainGate_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the Main Gate

**Claim.** The profile main gate at coordinate $i$ is a linear threshold function.

**Proof.** Split according to whether $a(i+1)=a(i)$. In that case the gate is constantly $1$, so it is a linear threshold function by the constant-gate result (\texttt{FABL.constantThresholdGate_isLinearThreshold}). If the signs differ, split according to whether $a(i+1)=1$. When it equals $1$, the gate is the count threshold gate at level $i+1$, which is a linear threshold function by \texttt{FABL.countThresholdGate_isLinearThreshold}. In the other case the gate is the negated count threshold gate at the same level, covered by \texttt{FABL.negCountThresholdGate_isLinearThreshold}. Hence the main gate is a linear threshold function in every case.

**Key facts.** `FABL.constantThresholdGate_isLinearThreshold`, `FABL.countThresholdGate_isLinearThreshold`, `FABL.negCountThresholdGate_isLinearThreshold`.
