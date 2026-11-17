<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.Out.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity Outside a Finite Interval

**Claim.** If $M$ agrees with $M'$ outside the specified finite interval and $M'$ agrees with $M''$ there, then $M$ agrees with $M''$ outside that interval.

**Proof.** Fix an integer $z$ outside the specified set. At $z$, the second agreement gives $M''(z)=M'(z)$, while the first gives $M'(z)=M(z)$. By transitivity of equality, $M''(z)=M(z)$, as required.
