<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.constantThresholdGate_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Functions as Linear Thresholds

**Claim.** Every constant Boolean function on the sign cube is a linear threshold function, with zero weights and an offset whose threshold sign is the constant value.

**Proof.** A sign is either $1$ or $-1$. If the constant value is $1$, take offset $1$ and all coordinate weights zero; the threshold input is always positive, so its sign is $1$. If the value is $-1$, take offset $-1$ and all weights zero; the threshold input is always negative, so its sign is $-1$. These choices give the required representation at every input.
