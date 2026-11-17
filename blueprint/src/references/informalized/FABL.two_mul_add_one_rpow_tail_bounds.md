<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.two_mul_add_one_rpow_tail_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Bounds for a Power Tail

**Claim.** For every real $s<-1$ and natural number $q$, the integral of $(2x+1)^s$ over $x>q+1$ is at most the series of its values at the odd integers beginning with $2q+3$, and that series is at most the integral over $x>q$.

**Proof.** Let $f(x)=(2x+1)^s$. Since $s<-1$, we have $s\leq 0$, so $f$ is antitone on $[0,\infty)$ by the monotonicity fact for this power function (`FABL.antitoneOn_two_mul_add_one_rpow`). Also, $f$ is integrable on every tail $x>a$ for $a\geq0$ by `FABL.integrableOn_two_mul_add_one_rpow`; the same integrability gives summability of its sampled values. Apply the integral-to-series comparison for a nonnegative antitone function on the tail beginning at $q+1$: its integral there is at most the sum of its values at $q+1,q+2,\ldots$. Apply the reverse series-to-integral comparison on the tail beginning at $q$: that sum, starting at $q+1$, is at most the integral there. Finally, rewriting $f(r+q+1)$ gives $(2(r+q+1)+1)^s$, as required.

**Key facts.** `FABL.antitoneOn_two_mul_add_one_rpow`, `FABL.integrableOn_two_mul_add_one_rpow`.
