<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.mul_choose_le_mul_choose_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Binomial Coefficients

**Claim.** For natural numbers $s,t,k$ with $s\le t$ and $k>0$, one has $t\binom{s}{k}\le s\binom{t}{k}$.

**Proof.** First suppose $k\le s$. Since $k>0$, both $s$ and $t$ are positive; write $s=s'+1$, $t=t'+1$, and $k=k'+1$. Then $s'\le t'$, hence $\binom{s'}{k'}\le\binom{t'}{k'}$. The identity $(m+1)\binom{m}{r+1}=(r+1)\binom{m+1}{r+1}$ converts the desired inequality into this comparison after multiplying both sides by the positive number $k'+1$. If instead $k>s$, then also $k> s$ forces $\binom{s}{k}=0$, so the left side is zero and the inequality follows.
