<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.abs_rpow_le_two_rpow_mul_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound for a Bounded Real Number

**Claim.** If $|z|\le2$ and $p\ge2$, then $|z|^p\le2^p z^2$.

**Proof.** Set $a=|z|$, so $0\le a\le2$. If $a=0$, then $z=0$ and both sides are zero. Otherwise $a>0$, and $p-2\ge0$. Monotonicity of real powers in the base gives $a^{p-2}\le2^{p-2}$, while monotonicity in the exponent for base $2$ gives $2^{p-2}\le2^p$. Factor $a^p=a^2a^{p-2}$ and use $a^2=z^2$. Multiplying the power bounds by the nonnegative number $z^2$ yields $|z|^p\le2^p z^2$.
