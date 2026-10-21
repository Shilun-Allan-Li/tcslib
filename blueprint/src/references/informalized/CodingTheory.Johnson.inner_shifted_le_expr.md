<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: CodingTheory.Johnson.inner_shifted_le_expr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Upper bound on the shifted inner product

**Claim.** Let $x,y$ be binary words of length $n$ and let $\alpha\ge 0$. Suppose the Hamming distance between $x$ and $y$ is at least $d$ and the Hamming weights of $x$ and $y$ are each at most $w$. Write $\hat{x}^\alpha$ and $\hat{y}^\alpha$ for the shifted vectors in $\mathbb{R}^n$, i.e. the $\pm 1$ embedding of each word minus $\alpha$ times the all-ones vector. Then their Euclidean inner product satisfies
\[
\langle \hat{x}^\alpha, \hat{y}^\alpha \rangle \;\le\; (n-2d) + \alpha^2 n + 2\alpha\,(2w-n).
\]

**Proof.** The proof first computes the inner product *exactly*, as a function of the Hamming distance and the two weights, and then relaxes the three integer quantities to their stated bounds, using $\alpha\ge 0$ to keep the inequality pointing the right way.

**1. Expand the shifted inner product.** By definition $\hat{x}^\alpha = \mathrm{pm}(x) - \alpha\,\mathbf{1}$, where $\mathrm{pm}(x)\in\mathbb{R}^n$ is the $\pm 1$ embedding ($-1$ where $x$ is true, $+1$ otherwise) and $\mathbf{1}$ is the all-ones vector, and likewise for $y$. Bilinearity of the Euclidean inner product gives
\[
\langle \hat{x}^\alpha, \hat{y}^\alpha \rangle
= \langle \mathrm{pm}(x), \mathrm{pm}(y)\rangle
- \alpha\,\langle \mathrm{pm}(x), \mathbf{1}\rangle
- \alpha\,\langle \mathrm{pm}(y), \mathbf{1}\rangle
+ \alpha^2\,\langle \mathbf{1}, \mathbf{1}\rangle,
\]
which is the expansion lemma (`inner_shifted_expand`).

**2. Evaluate the three building-block inner products.** Three facts about the $\pm 1$ embedding and the all-ones vector supply the pieces:
- The embeddings of $x$ and $y$ agree in sign exactly on the positions where the words agree and differ in sign where they differ, so each matching coordinate contributes $+1$ and each mismatching coordinate $-1$; hence $\langle \mathrm{pm}(x), \mathrm{pm}(y)\rangle = n - 2\,\mathrm{hdist}(x,y)$ (`inner_pmOne_pmOne`).
- Summing the embedding of $x$ against the all-ones vector counts $+1$ for each $0$-bit and $-1$ for each $1$-bit, giving $\langle \mathrm{pm}(x), \mathbf{1}\rangle = n - 2\,\mathrm{wt}(x)$, and similarly for $y$ (`inner_pmOne_ones`).
- The all-ones vector has squared norm $\langle \mathbf{1}, \mathbf{1}\rangle = n$ (`inner_ones_ones`).

Substituting these into the expansion yields the exact identity
\[
\langle \hat{x}^\alpha, \hat{y}^\alpha \rangle
= \bigl(n - 2\,\mathrm{hdist}(x,y)\bigr)
- \alpha\bigl(n - 2\,\mathrm{wt}(x)\bigr)
- \alpha\bigl(n - 2\,\mathrm{wt}(y)\bigr)
+ \alpha^2 n .
\]

**3. Compare with the target bound.** Let $R = (n-2d) + \alpha^2 n + 2\alpha(2w-n)$ denote the claimed upper bound. Subtracting the exact value found in step 2 from $R$, the $n$, $\alpha^2 n$, and $-2\alpha n$ contributions all cancel, leaving
\[
R - \langle \hat{x}^\alpha, \hat{y}^\alpha \rangle
= 2\bigl(\mathrm{hdist}(x,y) - d\bigr)
+ 2\alpha\bigl((w - \mathrm{wt}(x)) + (w - \mathrm{wt}(y))\bigr).
\]
Both terms are nonnegative: the first because $d \le \mathrm{hdist}(x,y)$, and the second because $\alpha \ge 0$ while $\mathrm{wt}(x) \le w$ and $\mathrm{wt}(y) \le w$. Hence $R - \langle \hat{x}^\alpha, \hat{y}^\alpha \rangle \ge 0$, which is exactly the asserted inequality. (In the Lean source this final linear-arithmetic step is handled by `nlinarith`, fed the three bounds recast as real inequalities; the sign of $\alpha$ is what makes the weight terms work in its favour.) $\qquad\blacksquare$

**Key facts.** `CodingTheory.Johnson.inner_shifted_expand`, `CodingTheory.Johnson.inner_pmOne_pmOne`, `CodingTheory.Johnson.inner_pmOne_ones`, `CodingTheory.Johnson.inner_ones_ones`.
