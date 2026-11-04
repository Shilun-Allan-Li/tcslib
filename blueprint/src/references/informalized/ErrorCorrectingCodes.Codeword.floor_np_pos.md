<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: ErrorCorrectingCodes.Codeword.floor_np_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Positivity of ⌊np⌋ for large n

**Claim.** Let $p$ be a real number with $0 < p$ and $0 < 1-p$ (so that $0 < p < 1$), and put $N_2 = \lceil 2/(p(1-p))\rceil + 1$. Then for every natural number $n$ with $N_2 \le n$, the floor $\lfloor np\rfloor$ — taken as a natural number — is strictly positive, equivalently $\lfloor np\rfloor \ge 1$.

**Proof.** The floor in question is the natural-number floor $\lfloor np\rfloor \in \mathbb{N}$, and a natural number is positive exactly when it is nonzero. So it suffices to rule out $\lfloor np\rfloor = 0$; we argue by contradiction, assuming $\lfloor np\rfloor = 0$ and deriving an absurdity.

1. **Translate the assumption into an inequality.** For the natural-number floor one has $\lfloor x\rfloor = 0$ if and only if $x < 1$ (`Nat.floor_eq_zero`). Hence the assumption $\lfloor np\rfloor = 0$ gives
\[
n p < 1.
\]
Note also that $0 < p$ and $0 < 1-p$ give $0 < p(1-p)$, a positive quantity we may freely multiply by.

2. **A lower bound on $n$ from the definition of $N_2$.** Since the ceiling of a real never undershoots it, $\lceil 2/(p(1-p))\rceil \ge 2/(p(1-p))$ (`Nat.le_ceil`). Adding $1$ and using $N_2 = \lceil 2/(p(1-p))\rceil + 1$ gives
\[
N_2 \;\ge\; \frac{2}{p(1-p)} + 1 .
\]
The hypothesis $N_2 \le n$ (read over the reals) then yields
\[
n \;\ge\; \frac{2}{p(1-p)} + 1 .
\]

3. **Clear the denominator.** Multiplying the last inequality by the nonnegative factor $p(1-p)$ and simplifying $\bigl(2/(p(1-p)) + 1\bigr)\cdot p(1-p) = 2 + p(1-p)$, we obtain
\[
n\,p(1-p) \;\ge\; 2 + p(1-p) .
\]
In particular $n\,p(1-p) > 2$, because $p(1-p) > 0$.

4. **An upper bound on the same product.** Rewrite $n\,p(1-p) = (np)(1-p)$. Since $np < 1$ (Step 1) and $1-p > 0$, multiplying these gives $(np)(1-p) < 1\cdot(1-p) = 1-p$, and $1-p < 1$ because $p > 0$. Thus
\[
n\,p(1-p) \;<\; 1 .
\]

5. **Contradiction.** Steps 3 and 4 together force $2 < n\,p(1-p) < 1$, which is impossible. This contradiction refutes the assumption $\lfloor np\rfloor = 0$, so $\lfloor np\rfloor > 0$, i.e. $\lfloor np\rfloor \ge 1$. $\qquad\blacksquare$

(The final contradiction is discharged mechanically from the two bounds together with the positivity of $p(1-p)$; the arithmetic is exactly the squeeze $2 < n\,p(1-p) < 1$ displayed above.)
