<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.neg_emod_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated Natural Remainder

**Claim.** For natural numbers $a$ and $M$ with $1\le M$, the integer remainder of $-a$ modulo $M$ is zero if $a$ has natural remainder zero, and otherwise is $M-(a\bmod M)$.

**Proof.** Write the natural division algorithm as $a=Mq+r$, where $q=a/M$ and $r=a\bmod M$. The natural remainder bound gives $0\le r<M$. If $r=0$, then $-a=-Mq$, so its remainder modulo $M$ is zero. If $r\ne0$, rewrite $-a=(M-r)+M(-q-1)$. Since $0<r<M$, the number $M-r$ lies strictly between $0$ and $M$; it is therefore the canonical integer remainder of $-a$ modulo $M$.
