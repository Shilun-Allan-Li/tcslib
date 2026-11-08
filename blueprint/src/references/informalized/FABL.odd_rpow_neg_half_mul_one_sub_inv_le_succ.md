<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.odd_rpow_neg_half_mul_one_sub_inv_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-arity power inequality

**Claim.** For every odd natural number $k$, $k^{-1/2}(1-1/k)\le (k+2)^{-1/2}$.

**Proof.** Write $k=2q+1$ and let $K$ be its real value. Then $K\ge1$, so both $K$ and $K+2$ are positive. The odd-arity identity (\texttt{oddArity\_rpow\_neg\_one\_half}) rewrites $K^{-1/2}$ as $1/\sqrt K$, and the negative-power rule rewrites $(K+2)^{-1/2}$ as $1/\sqrt{K+2}$. Both sides are nonnegative: in particular, $1-1/K\ge0$. Thus it suffices to compare their squares. These are $(K-1)^2/K^3$ and $1/(K+2)$, respectively. Since the denominators are positive, the desired comparison reduces to $(K-1)^2(K+2)\le K^3$, which follows by expansion (the difference of the right side and left side is $3K-2\ge0$).

**Key facts.** `FABL.oddArity_rpow_neg_one_half`.
