<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.width_ac0ThresholdParityCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold-Parity Circuit Width

**Claim.** For every integer $m\ge 7$, the width of the specified threshold-parity circuit is exactly $2m$.

**Proof.** The circuit's width is the width of its first-layer DNF. The first-layer width theorem gives this as $m+m$ (blockFirstLayer_width). Since $m+m=2m$, the claimed width follows.

**Key facts.** `FABL.blockFirstLayer_width`.
