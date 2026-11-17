<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.two_mul_midpoint_mul_logb_inv_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Midpoint logarithmic inequality

**Claim.** For nonnegative real numbers $a$ and $b$, twice their arithmetic mean multiplied by the base-$2$ logarithm of the reciprocal of their arithmetic mean is at most the sum of $a$ times the base-$2$ logarithm of $1/a$, $b$ times the base-$2$ logarithm of $1/b$, and $|a-b|$.

**Proof.** First handle the cases where one of $a,b$ is zero. If both vanish, the inequality reduces to equality. If, say, $a=0<b$, then the midpoint is $b/2$, whose reciprocal is $2/b$. The logarithm rule $\log_2(2/b)=1+\log_2(1/b)$ reduces the desired inequality to an immediate comparison using $|a-b|=b$; the case $b=0<a$ is symmetric. Now suppose both are positive and set $s=a+b$ and $p=a/s$. Then $p\in[0,1]$. The binary-entropy estimate $1\le H(p)/\log 2+|2p-1|$ (\texttt{FABL.one_le_binEntropy_div_log_two_add_abs}) applies. Multiplying by $s\log 2>0$ gives $s\log 2\le sH(p)+s|2p-1|\log 2$. Expanding the entropy at $p=a/s$ gives $sH(p)=a\log(1/a)+b\log(1/b)-s\log(1/s)$, while direct simplification gives $s|2p-1|=|a-b|$. Also, $\log(2/s)=\log 2+\log(1/s)$. Substituting these identities into the scaled estimate yields $s\log(2/s)\le a\log(1/a)+b\log(1/b)+|a-b|\log 2$. Finally divide by the positive number $\log 2$ and use $\log_2 t=\log t/\log 2$; since twice the midpoint is $s$, this is precisely the claimed inequality.

**Key facts.** `FABL.one_le_binEntropy_div_log_two_add_abs`.
