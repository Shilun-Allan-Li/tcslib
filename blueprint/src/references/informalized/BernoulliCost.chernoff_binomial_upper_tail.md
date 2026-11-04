<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: BernoulliCost.chernoff_binomial_upper_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A Chernoff upper-tail bound for the binomial distribution

**Claim.** Fix a natural number $n$ and a real $p$ with $0 < p \le 1$. Writing the binomial probability mass as $\binom{n}{k}p^k(1-p)^{n-k}$, the total mass carried by the indices $k \in \{0,1,\dots,n\}$ with $k > 2np$ is at most $e^{-np/3}$. In probabilistic terms, $\Pr[\mathrm{Bin}(n,p) > 2np] \le e^{-np/3}$: the chance that a binomial variable exceeds twice its mean decays exponentially in the mean.

**Proof.** The argument splits on the size of $p$. The interesting case is $p \le \tfrac12$, handled by a Chernoff (exponential moment) estimate with a *fixed*, unoptimised parameter $t = \log 2$; the case $p > \tfrac12$ is disposed of because the tail is then empty.

**Case $p \le \tfrac12$.** The engine is the elementary bound $\mathbf 1[k > a] \le e^{t(k-a)}$, valid for any threshold $a$ and any $t>0$. We take $a = 2np$ and $t = \log 2$, so that $e^{t} = 2$.

1. **The moment generating function is a binomial.** By the binomial theorem $(x+y)^n = \sum_{k=0}^n \binom{n}{k}x^k y^{n-k}$ (`add_pow`), applied with $x = p\,e^{\log 2}$ and $y = 1-p$,
\[
\sum_{k=0}^{n}\binom{n}{k}p^{k}(1-p)^{n-k}e^{k\log 2}
=\bigl(p\,e^{\log 2}+(1-p)\bigr)^{n},
\]
since $p^k e^{k\log 2} = (p\,e^{\log 2})^k$.

2. **Bound the MGF by a single exponential.** Write the base as $1 + p(e^{\log 2}-1)$; because $0<p\le 1$ this base is positive, so the power equals $\exp\!\bigl(n\log(1+p(e^{\log 2}-1))\bigr)$. The bound $\log x \le x-1$ (`Real.log_le_sub_one_of_pos`) gives $\log\!\bigl(1+p(e^{\log 2}-1)\bigr) \le p(e^{\log 2}-1)$, hence
\[
\sum_{k=0}^{n}\binom{n}{k}p^{k}(1-p)^{n-k}e^{k\log 2}
\le \exp\!\bigl(np(e^{\log 2}-1)\bigr).
\]
(Positivity of the base uses $e^{\log 2} > 1$, which follows from $1+x\le e^x$, i.e. `Real.add_one_le_exp`.)

3. **Insert the threshold.** Multiplying both sides by the positive constant $e^{-2np\log 2}$ and folding it into each summand via $e^{k\log 2}e^{-2np\log 2}=e^{(k-2np)\log 2}$ yields
\[
\sum_{k=0}^{n}\binom{n}{k}p^{k}(1-p)^{n-k}e^{(k-2np)\log 2}
\le \exp\!\bigl(np(e^{\log 2}-1)-2np\log 2\bigr).
\]

4. **Simplify the exponent to $-np/3$.** Since $e^{\log 2}=2$, the exponent collapses to $np(2-1)-2np\log 2 = np\,(1-2\log 2)$. As $np \ge 0$, to get $np(1-2\log 2) \le -np/3$ it suffices that $1-2\log 2 \le -\tfrac13$, i.e. $\log 2 \ge \tfrac23$. This holds because $\log 2 = 0.6931\ldots > 0.6\overline{6}$ (the numeric lower bound `Real.log_two_gt_d9`). Therefore the right-hand side of Step 3 is at most $e^{-np/3}$.

5. **Drop to the tail terms.** Compare the target sum, restricted to $k > 2np$, with the full weighted sum of Step 3. For an index $k > 2np$ the weight satisfies $e^{(k-2np)\log 2} \ge 1$ (the exponent is nonnegative since $\log 2 > 0$), so the plain summand is $\le$ its weighted version; for every other $k$ the weighted summand is still nonnegative and only adds to the full sum. All binomial summands are nonnegative here because $0 \le p$ and $1-p \ge 0$. Chaining these comparisons,
\[
\sum_{\substack{0\le k\le n\\ k > 2np}}\binom{n}{k}p^{k}(1-p)^{n-k}
\;\le\;
\sum_{k=0}^{n}\binom{n}{k}p^{k}(1-p)^{n-k}e^{(k-2np)\log 2}
\;\le\; e^{-np/3},
\]
which is the claim.

**Case $p > \tfrac12$.** Here the tail is empty, so the sum is $0 \le e^{-np/3}$. If $n=0$ the index set $\{0\}$ already fails the condition $k > 0$. If $n \ge 1$, then for every $k \le n$ we have $(k:\mathbb R) \le n < 2np$, because $2p > 1$ forces $2np > n$; hence no admissible $k$ satisfies $k > 2np$ and the filtered sum is empty. Nonnegativity of $e^{-np/3}$ finishes it.
