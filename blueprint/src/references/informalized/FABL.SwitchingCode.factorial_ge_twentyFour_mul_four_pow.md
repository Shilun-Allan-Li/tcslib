<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.factorial_ge_twentyFour_mul_four_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Lower Bound

**Claim.** For every integer $i\geq4$, one has $24\cdot4^{i-4}\leq i!$.

**Proof.** Write $i=4+t$ with $t\geq0$ and induct on $t$. At $t=0$ the inequality is $24\leq4!$, an equality. If it holds for $t$, then $(4+t+1)!=(4+t+1)(4+t)!$. Since $4+t+1\geq4$, multiplying the induction bound by this factor gives $(4+t+1)!\geq24\cdot4^t\cdot4=24\cdot4^{t+1}$, as required.
