<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.choose_mul_pow_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A binomial-coefficient and power inequality via induction on the exponent

**Claim.** Let $n$, $s$, $d$ be natural numbers with $5s \le n$ and $d \le s$. Then
\[
  \binom{n}{s-d}\,(4n)^d \;\le\; \binom{n}{s}\,(5s)^d .
\]
Thus lowering the lower index by $d$ while trading a factor of $4n$ for a factor of $5s$ at each step never increases the product; the hypothesis $5s \le n$ is exactly what makes the exchange rate favourable.

**Proof.** The argument is an induction on the exponent $d$. The whole content lives in a single one-step inequality, which is then amplified to the power $d+1$ by multiplying through by the inductive hypothesis.

**1. Base case $d = 0$.** Both powers are $1$ and both lower indices are $s$, so the claim reads $\binom{n}{s} \le \binom{n}{s}$, which holds with equality.

**2. The one-step inequality.** The heart of the inductive step is the claim
\[
  \binom{n}{\,s-d-1\,}\,(4n) \;\le\; \binom{n}{\,s-d\,}\,(5s).
\tag{$\star$}
\]
Write $m = s-d-1$, so that $s-d = m+1$ and (since $d \le s-1$ in the inductive step) $m \ge 0$, $m \le n$, and $m+1+d = s$. The point is to convert the two neighbouring binomial coefficients into one another using the elementary recurrence
\[
  \binom{n}{m+1}\,(m+1) \;=\; \binom{n}{m}\,(n-m),
\]
the fact that absorbing an extra element into a size-$(m{+}1)$ subset counts the same both ways (`Nat.choose_succ_right_eq`). With this identity in hand, $(\star)$ — that is, $\binom{n}{m}\,4n \le \binom{n}{m+1}\,5s$ — follows once we establish the purely arithmetic inequality
\[
  4n\,(m+1) \;\le\; (n-m)\,(5s).
\tag{$\dagger$}
\]
Indeed, multiplying $(\dagger)$ by $\binom{n}{m}$ and applying the recurrence to the right-hand side gives
\[
  \binom{n}{m}\,4n\,(m+1) \;\le\; \binom{n}{m}(n-m)\,5s \;=\; \binom{n}{m+1}(m+1)\,5s,
\]
and cancelling the positive factor $m+1$ yields $(\star)$. (The positivity $\binom{n}{m} > 0$ that justifies treating the coefficients as honest nonnegative multipliers comes from $m \le n$, via `Nat.choose_pos`.)

**3. Proof of the arithmetic inequality $(\dagger)$.** Here natural subtraction must be handled with care, so we work over the integers, legitimate because $m \le n$ makes $n-m$ a genuine difference. Using $m+1 = s-d \le s$ and $m \le s-1$, expand
\[
  (n-m)\,5s - 4n\,(m+1) \;=\; 5sn - 4n - m\,(5s+4n).
\]
Bounding $m \le s-1$ in the subtracted term and simplifying gives
\[
  5sn - 4n - m\,(5s+4n) \;\ge\; 5sn - 4n - (s-1)(5s+4n) \;=\; s\,(n - 5s) + 5s,
\]
which is $\ge 0$ precisely because $5s \le n$. (This step is where the governing hypothesis $5s \le n$ is spent.) Hence $(\dagger)$, and therefore $(\star)$, holds.

**4. Amplifying to the step for $d+1$.** Assume the inequality for $d$. Applying the inductive hypothesis — permissible since $d+1 \le s$ forces $d \le s$ — gives
\[
  \binom{n}{s-d}\,(4n)^d \;\le\; \binom{n}{s}\,(5s)^d .
\tag{IH}
\]
The goal for $d+1$ involves the lower index $s-(d+1) = s-d-1$ (a trivial rewriting of nested subtraction) and the powers $(4n)^{d+1} = 4n\cdot(4n)^d$, $(5s)^{d+1} = 5s\cdot(5s)^d$. Chaining the two established facts:
\[
  \binom{n}{s-d-1}\,4n\,(4n)^d
  \;\overset{(\star)}{\le}\;
  \binom{n}{s-d}\,5s\,(4n)^d
  \;\overset{\text{(IH)}}{\le}\;
  \binom{n}{s}\,(5s)^d\,5s ,
\]
where the first inequality multiplies $(\star)$ by the nonnegative factor $(4n)^d$ and the second multiplies (IH) by $5s$. The two outer terms are exactly $\binom{n}{s-(d+1)}(4n)^{d+1}$ and $\binom{n}{s}(5s)^{d+1}$, completing the induction. (The multiplications require $(4n)^d > 0$, which holds since $4n > 0$ — a consequence of $0 < 5s \le n$ in the non-trivial case.)

**Key facts.** `Nat.choose_succ_right_eq`, `Nat.choose_pos`, `Nat.sub_add_cancel`, `Nat.sub_sub`, `pow_succ'`, `pow_pos`.
