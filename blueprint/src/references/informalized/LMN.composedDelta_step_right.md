<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: LMN.composedDelta_step_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Depth recursion for the composed Bernoulli restriction parameter

**Claim.** Fix a fan-in bound $w$, a width parameter $l>0$, and a depth $d\ge 3$, and write $\delta(w,l,d)=\frac{1}{40w}\left(\frac{1}{40l}\right)^{d-2}$ for the composed Bernoulli restriction parameter at those values. Then lowering the depth by one strips off exactly one factor of $1/(40l)$: $\delta(w,l,d)=\delta(w,l,d-1)\cdot\frac{1}{40l}$.

**Proof.** The whole claim is the exponent identity
\[
  \left(\frac{1}{40l}\right)^{d-2}
  =
  \left(\frac{1}{40l}\right)^{(d-1)-2}\cdot\frac{1}{40l},
\]
since the common scalar factor $\tfrac{1}{40w}$ appears unchanged on both sides and so may be factored out. The one genuine point is that the exponents here are *truncated* natural-number subtractions, and the hypothesis $d\ge 3$ is exactly what makes them behave like honest subtraction.

The proof proceeds by exhausting the small values of $d$ and reducing the one surviving case to a single step of the power law.

1. **Discard the impossible depths.** Split on the value of $d$. If $d=0$ or $d=1$, the hypothesis $d\ge 3$ is already false, so these branches close by contradiction with nothing to prove. This leaves $d\ge 2$, which we write as $d=k+2$.

2. **Discard one more.** With $d=k+2$ the hypothesis reads $k+2\ge 3$, i.e. $k\ge 1$. Splitting once more on $k$: the value $k=0$ gives $d=2$, which again contradicts $d\ge 3$ and closes. So we are left with $k\ge 1$, that is, $d=m+3$ for some $m\ge 0$.

3. **The surviving case is one power step.** For $d=m+3$ both exponents are honest: $d-2=m+1$ and $(d-1)-2=m$. The identity to prove becomes
\[
  \left(\frac{1}{40l}\right)^{m+1}
  =
  \left(\frac{1}{40l}\right)^{m}\cdot\frac{1}{40l},
\]
which is exactly the power law $a^{m+1}=a^{m}\cdot a$ (`pow_succ'`) with $a=\tfrac{1}{40l}$. Reinstating the untouched scalar $\tfrac{1}{40w}$ and rearranging the resulting product of real numbers gives
\[
  \delta(w,l,d)=\frac{1}{40w}\left(\frac{1}{40l}\right)^{m+1}
  =\left(\frac{1}{40w}\left(\frac{1}{40l}\right)^{m}\right)\cdot\frac{1}{40l}
  =\delta(w,l,d-1)\cdot\frac{1}{40l},
\]
as claimed. The final rearrangement is a routine commutative-ring calculation.

The reason the argument is organized as this double case-split rather than a one-line manipulation is that the identity it reduces to, $a^{d-2}=a^{(d-1)-2}\cdot a$, only holds once truncated subtraction is pinned down: the exhaustion of $d\in\{0,1,2\}$ clears the depths where $d-2$ or $(d-1)-2$ would collapse to $0$, and the leftover case $d=m+3$ writes the exponent as an explicit successor $m+1$ so that the power law applies directly.
