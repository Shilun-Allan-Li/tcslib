<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: ErrorCorrectingCodes.Codeword.listDecoding_counting_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A counting inequality for list decoding at the Elias–Bassalygo rate

**Claim.** Fix an integer alphabet size $q \ge 2$, a real number $p$, and integers $n$ and $L \ge 1$, and write $H_q(p)$ for the $q$-ary entropy. Set the rate $r = 1 - H_q(p) - \tfrac{1}{L}$, and put $M = \lfloor q^{rn}\rfloor$ and $V = \lfloor q^{H_q(p)\,n}\rfloor$. Assuming $0 < M \le q^n$ and $L < M$, the inequality $q^n \cdot \binom{V}{L+1}\cdot\binom{q^n-(L+1)}{M-(L+1)} < \binom{q^n}{M}$ holds. This is the combinatorial heart of the list-decoding capacity argument: it says that the obvious union bound over choices of a bad list of $L+1$ codewords, weighted by the number of codes extending such a list, falls strictly short of the total number of codes.

**Proof.** Write $H = H_q(p)$ throughout. The whole proof amounts to bounding the left-hand side by three elementary estimates and checking that the resulting constant is strictly below $1$. We first divide both sides by $\binom{q^n}{M}$, which is legitimate and sign-preserving because $M \le q^n$ forces $\binom{q^n}{M} > 0$ (`Nat.choose_pos`).

**Step 1 — The binomial ratio bound.** Apply the counting lemma that for $k \le M \le N$ one has
\[
\frac{\binom{N-k}{M-k}}{\binom{N}{M}} \;\le\; \Bigl(\frac{M}{N}\Bigr)^{k}
\qquad(\texttt{binom\_ratio\_bound}),
\]
with $N = q^n$ and $k = L+1$. The two hypotheses are met: $M \le q^n$ is assumed, and $L < M$ gives $L+1 \le M$. Hence
\[
\binom{q^n-(L+1)}{M-(L+1)} \;\le\; \Bigl(\frac{M}{q^n}\Bigr)^{L+1}\binom{q^n}{M}.
\]

**Step 2 — The central binomial coefficient.** By the standard estimate $\binom{V}{L+1} \le V^{L+1}/(L+1)!$ (`Nat.choose_le_pow_div`), the factor $\binom{V}{L+1}$ is controlled by a pure power of $V$.

**Step 3 — Assembling the product.** Combining Steps 1 and 2, the left-hand side of the claim is at most
\[
q^n \cdot \frac{V^{L+1}}{(L+1)!}\cdot\Bigl(\frac{M}{q^n}\Bigr)^{L+1}\cdot\binom{q^n}{M}.
\]
So it suffices to prove that the leading constant
\[
P \;=\; q^n \cdot \frac{V^{L+1}}{(L+1)!}\cdot\Bigl(\frac{M}{q^n}\Bigr)^{L+1}
\]
is strictly less than $1$; multiplying such a bound by the positive integer $\binom{q^n}{M}$ then yields the strict inequality claimed.

**Step 4 — Replacing the floors by their real upper bounds.** Each of $V$ and $M$ is a floor, so $V \le q^{H n}$ and $M \le q^{rn}$ (both via $\lfloor x\rfloor \le x$ for $x \ge 0$, the non-negativity holding because the bases are positive). Since every factor of $P$ is non-negative and increasing in $V$ and $M$, we may substitute these upper bounds:
\[
P \;\le\; q^n \cdot \frac{\bigl(q^{H n}\bigr)^{L+1}}{(L+1)!}\cdot\Bigl(\frac{q^{rn}}{q^n}\Bigr)^{L+1}.
\]

**Step 5 — The exponent collapses to $-n/L$.** Collecting all powers of $q$ in the right-hand side gives exponent
\[
n + (L+1)\,n\,H + (L+1)\,n\,(r-1)
\;=\; n + (L+1)\,n\,\bigl(H + r - 1\bigr).
\]
By the definition of the rate, $H + r - 1 = H + \bigl(1 - H - \tfrac1L\bigr) - 1 = -\tfrac1L$, so the exponent equals
\[
n - (L+1)\frac{n}{L} \;=\; n\cdot\frac{L-(L+1)}{L} \;=\; -\frac{n}{L}.
\]
Therefore
\[
P \;\le\; \frac{q^{-n/L}}{(L+1)!}.
\]

**Step 6 — The constant is below $1$.** Two trivial facts finish the proof. First, the exponent $-n/L$ is non-positive (both $n$ and $L$ are non-negative), and the base $q \ge 1$, so $q^{-n/L} \le q^0 = 1$. Second, because $L \ge 1$ we have $(L+1)! \ge L+1 \ge 2$, hence $1/(L+1)! \le \tfrac12 < 1$. Multiplying,
\[
P \;\le\; \frac{q^{-n/L}}{(L+1)!} \;\le\; \frac{1}{(L+1)!} \;<\; 1.
\]
Feeding $P < 1$ back through Step 3 gives
\[
q^n \cdot \binom{V}{L+1}\cdot\binom{q^n-(L+1)}{M-(L+1)} \;\le\; P\cdot\binom{q^n}{M} \;<\; \binom{q^n}{M},
\]
which is exactly the assertion. $\qquad\blacksquare$

A remark on the route: the Lean proof never estimates $\binom{V}{L+1}$ and the two $q^n$-binomials separately against the right-hand side. Instead it isolates a single scalar $P$, bounds it above by substituting the real quantities $q^{Hn}$ and $q^{rn}$ for the integer floors $V$ and $M$, and reduces the whole inequality to the one-line exponent computation $H + r - 1 = -1/L$. This is why the hypotheses are shaped exactly so that the rate deficit $1/L$ appears: it is precisely the margin that drives $P$ strictly below $1$.

**Key facts.** `ErrorCorrectingCodes.Codeword.binom_ratio_bound`.
