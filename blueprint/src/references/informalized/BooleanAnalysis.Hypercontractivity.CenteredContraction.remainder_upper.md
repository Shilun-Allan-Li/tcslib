<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Global remainder bound

**Claim.** For each real $q\ge2$, there is a positive constant $M$ such that for every real $x$, $|1+x|^q-1-qx\le M(x^2+|x|^q)$.

**Proof.** Choose a natural number $m>q$ and set $M=2^m+2^q+q+1$, which is positive. If $|x|\le1$, the local remainder estimate (`remainder_local_upper`) bounds the remainder by $2^m x^2$, and this is at most $M(x^2+|x|^q)$.

If $|x|>1$, then $|1+x|\le1+|x|\le2|x|$. Since $q\ge0$, raising to the power $q$ gives $|1+x|^q\le2^q|x|^q$. Also $|x|\le|x|^q$. These bounds, together with $-qx\le q|x|$, show that the remainder is at most $(2^q+q)|x|^q$, which is at most $M(x^2+|x|^q)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_local_upper`.
