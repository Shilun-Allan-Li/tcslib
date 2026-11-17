<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.mono_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity Under Setting a Bit

**Claim.** Setting the value of $M$ at an integer $z$ to true preserves every location where $M$ was already true.

**Proof.** Fix an integer $z'$ with $M(z')=\mathrm{true}$. If $z'=z$, the updated function has value true there by its definition. If $z'\ne z$, the update leaves the value at $z'$ unchanged, so it remains true. This is precisely the claimed inclusion.
