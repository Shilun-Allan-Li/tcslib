<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.choose_final_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final-Block Term Bound

**Claim.** For all nonnegative integers $w$ and $i$, with $a_i=((2^i-1)(4/9)^i)/i!$ and $r_i=(4/9)^i/i!$, one has $\binom{w}{i}2^i\leq (9w/4)^i(a_i+r_i)$.

**Proof.** Use the standard binomial estimate $\binom{w}{i}\leq w^i/i!$. Multiplying by $2^i$ preserves the inequality, since the multiplier is nonnegative. The resulting expression is exactly $(9w/4)^i(a_i+r_i)$ after expanding the definitions; this is the scaling identity `scale_mul_finalCoefficient`.

**Key facts.** `FABL.SwitchingCode.scale_mul_finalCoefficient`.
