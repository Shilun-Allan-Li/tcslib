<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.hasDepthCircuit_ac0ThresholdParityTarget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit for a parity product

**Claim.** For \(m\ge 7\), the specified product of block dot-product parity signs on the \(2^m\)-coordinate sign cube is computed by a depth-three circuit with at most \((2^m)^3\) internal gates and width at most \(2m\).

**Proof.** Use the constructed circuit \(C=\texttt{ac0ThresholdParityCircuit}\,m\,h_m\), where \(h_m\) records the hypothesis \(m\ge7\). Its depth is three (\(\texttt{FABL.depth_ac0ThresholdParityCircuit}\)). Its size is at most \(m2^{2m}+2^m\) (\(\texttt{FABL.size_ac0ThresholdParityCircuit}\)); the numerical bound \(m2^{2m}+2^m\le(2^m)^3\) then gives the required size bound (\(\texttt{FABL.ac0ThresholdParityCircuit_size_le_cube}\)). Its width is exactly \(2m\), and hence at most \(2m\) (\(\texttt{FABL.width_ac0ThresholdParityCircuit}\)). Finally, its evaluation at every input agrees with the specified target function (\(\texttt{FABL.eval_ac0ThresholdParityCircuit}\)). These properties exhibit the required circuit.

**Key facts.** `FABL.depth_ac0ThresholdParityCircuit`, `FABL.size_ac0ThresholdParityCircuit`, `FABL.ac0ThresholdParityCircuit_size_le_cube`, `FABL.width_ac0ThresholdParityCircuit`, `FABL.eval_ac0ThresholdParityCircuit`.
