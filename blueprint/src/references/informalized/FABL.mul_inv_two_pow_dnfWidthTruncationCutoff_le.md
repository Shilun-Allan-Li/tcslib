<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.mul_inv_two_pow_dnfWidthTruncationCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Cutoff Reciprocal Bound

**Claim.** For positive $s$ and $\varepsilon$, if $W$ is the width cutoff, then $s\,2^{-W}\le\varepsilon$.

**Proof.** Set $r=s/\varepsilon$, which is positive. By the defining property of the ceiling, $\log_2 r\le W$. Since the base $2$ is greater than $1$, exponentiation preserves order, giving $r\le2^W$. Multiplying by positive $\varepsilon$ yields $s\le\varepsilon 2^W$. Finally divide by the positive number $2^W$ to obtain $s\,2^{-W}\le\varepsilon$.
