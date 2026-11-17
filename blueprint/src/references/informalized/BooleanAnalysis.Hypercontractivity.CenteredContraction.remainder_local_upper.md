<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_local_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local real-power remainder bound

**Claim.** If $q\ge2$, $q\le m$ for a natural number $m$, and $|x|\le1$, then $|1+x|^q-1-qx\le 2^m x^2$.

**Proof.** The assumptions imply $m>0$ and $1+x\ge0$. Set $r=q/m$, so $0\le r\le1$. The Bernoulli inequality for exponents in this range, applied to $(1+x)^m-1\ge0$, gives
\[
(1+x)^q-1\le \frac qm\bigl((1+x)^m-1\bigr).
\]
After subtracting $qx$, this bounds the desired remainder by $q/m$ times the integer-power remainder. By the integer-power remainder bound (`pow_remainder_bound`), that remainder is at most $(2^m-1-m)x^2$, hence at most $2^m x^2$. Since $0\le q/m\le1$ and $x^2\ge0$, the resulting bound is at most $2^m x^2$. Finally, $1+x\ge0$ lets us replace $|1+x|^q$ by $(1+x)^q$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.pow_remainder_bound`.
