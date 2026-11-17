<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.linear_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity forces normalization

**Claim.** Every additive function $f$ satisfies $f(0)=0$.

**Proof.** Apply additivity to $0+0=0$. It gives $f(0)=f(0)+f(0)$; cancellation in the additive group yields $f(0)=0$, which is the required normalization.
