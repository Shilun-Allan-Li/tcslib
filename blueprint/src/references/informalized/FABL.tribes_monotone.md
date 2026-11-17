<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.tribes_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of tribes

**Claim.** For all nonnegative integers $w,s$, the tribes function is monotone: coordinatewise increase of the input in the order $-1<1$ cannot decrease its output.

**Proof.** Suppose $x\le y$ coordinatewise. Fix any block. Each coordinate of the block extracted from $x$ is at most the corresponding coordinate of the block extracted from $y$. Monotonicity of the AND function therefore gives that the AND value of this block at $x$ is at most its value at $y$. This holds for every block, so monotonicity of the OR function gives $\mathrm{Tribes}_{w,s}(x)\le \mathrm{Tribes}_{w,s}(y)$.

**Key facts.** `FABL.orFunction_monotone`, `FABL.andFunction_monotone`.
