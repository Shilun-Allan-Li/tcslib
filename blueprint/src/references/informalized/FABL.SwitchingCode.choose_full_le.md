<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.choose_full_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full-Block Term Bound

**Claim.** For all nonnegative integers $w$ and $i$, with $a_i=((2^i-1)(4/9)^i)/i!$, one has $\binom{w}{i}(2^i-1)\leq (9w/4)^i a_i$.

**Proof.** Apply the standard binomial estimate $\binom{w}{i}\leq w^i/i!$ and multiply by the nonnegative factor $2^i-1$. The resulting expression equals $(9w/4)^i a_i$ by the scaling identity `scale_mul_fullCoefficient`.

**Key facts.** `FABL.SwitchingCode.scale_mul_fullCoefficient`.
