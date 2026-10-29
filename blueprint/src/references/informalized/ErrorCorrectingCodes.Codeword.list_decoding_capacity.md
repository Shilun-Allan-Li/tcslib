<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: ErrorCorrectingCodes.Codeword.list_decoding_capacity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Existence of q-ary Codes at the List-Decoding Capacity Rate

**Claim.** Let $\alpha$ be a finite field with $q = |\alpha|$ elements, fix a real number $p$ with $0 < p \le 1 - \tfrac1q$ and an integer $L \ge 1$, and set the rate $r = 1 - H_q(p) - \tfrac1L$, where $H_q(p) = p\log_q(q-1) - p\log_q p - (1-p)\log_q(1-p)$ is the $q$-ary entropy. Then for every block length $n$ there exists a block code $C \subseteq \alpha^n$ with at least $M = \lfloor q^{rn}\rfloor$ codewords that is list-decodable from a $p$-fraction of symbol errors with lists of size at most $L$: every Hamming ball of radius $\lfloor pn\rfloor$ meets $C$ in at most $L$ codewords.

**Proof.** Throughout write $N = q^n = |\alpha^n|$ for the total number of codewords and recall that list-decodability of $C$ means $|B(\lfloor pn\rfloor, y)\cap C| \le L$ for every $y \in \alpha^n$, where $B(\ell, y)$ is the Hamming ball of radius $\ell$ about $y$. Since $\alpha$ is a nontrivial finite field we have $q \ge 2$, hence $q > 1$ as a real number; the various casts ($q > 0$, $q \ge 1$) are routine.

1. **The rate satisfies $r \le 1$, and $M \le N$.** In the stated regime $0 < p \le 1-\tfrac1q$ the $q$-ary entropy is strictly positive (`qary_entropy_pos`), and $\tfrac1L \ge 0$, so $r = 1 - H_q(p) - \tfrac1L \le 1$. Because $q \ge 1$, raising to a smaller exponent only shrinks the power, giving $q^{rn} \le q^n$; taking floors, $M = \lfloor q^{rn}\rfloor \le q^n = N$. Thus a code of size $M$ can always be carved out of $\alpha^n$. We split on whether $M$ is already small enough to be harmless.

2. **Trivial case $M \le L$.** Choose any subset $C \subseteq \alpha^n$ with exactly $M$ codewords; this is possible since $M \le N$ (`Finset.exists_subset_card_eq`). For every center $y$ the intersection $B(\lfloor pn\rfloor, y)\cap C$ is a subset of $C$, so its size is at most $|C| = M \le L$. Hence $C$ is list-decodable with list size $L$, and $|C| = M$. This settles the case with no counting at all.

3. **Substantive case $L < M$.** Here we must genuinely exhibit a good code. Introduce the ball-volume parameter $V = \lfloor q^{H_q(p)\,n}\rfloor$.

4. **Every Hamming ball holds at most $V$ codewords.** The entropy volume bound (`hamming_ball_size_asymptotic_upper_bound`) states that a Hamming ball of radius $\lfloor pn\rfloor$ in $\alpha^n$ contains at most $q^{H_q(p)\,n}$ points. Since the number of points is an integer bounded by this real, it is at most $\lfloor q^{H_q(p)\,n}\rfloor = V$. So $|B(\lfloor pn\rfloor, y)| \le V$ for all $y$.

5. **The counting inequality.** The heart of the argument is the estimate (`listDecoding_counting_ineq`)
\[
q^n \binom{V}{L+1}\binom{q^n - (L+1)}{\,M - (L+1)\,} \;<\; \binom{q^n}{M}.
\]
Read it as a union bound over $M$-element codes. The right-hand side counts all codes of size $M$ (choices of $M$ codewords from $N = q^n$). The left-hand side over-counts the *bad* codes — those for which some ball of radius $\lfloor pn\rfloor$ contains $L+1$ codewords, i.e. codes that fail list-decodability: first pick the offending center ($q^n$ choices), then pick $L+1$ codewords lying inside that ball (at most $\binom{V}{L+1}$ possibilities by Step 4), then fill in the remaining $M-(L+1)$ codewords arbitrarily from the other points. Since every bad code is counted this way, the number of bad codes is at most the left-hand side; the strict inequality then forces a good code of size $M$ to exist. The subtracted $\tfrac1L$ in the rate is precisely what makes this close: heuristically $\binom{V}{L+1}\approx q^{H_q(p)n(L+1)}$ and $\binom{N-(L+1)}{M-(L+1)}/\binom{N}{M}\approx (M/N)^{L+1}\approx q^{(r-1)n(L+1)}$, so the left side is about a $q^{\,n + (H_q(p)+r-1)n(L+1)} = q^{-n/L}$ fraction of the right side — a vanishing proportion, leaving room for the inequality to hold.

6. **Extracting the code.** Feeding the ball bound of Step 4 and the counting inequality of Step 5 into the existence lemma (`exists_listDecodable_code`), together with the side conditions $0 \le p \le 1$ (the upper bound is $p < 1$ via `lt_one_of_le_one_sub_inv`), $M \le N$, and $L < M$, produces a code $C \subseteq \alpha^n$ with exactly $M$ codewords that is list-decodable from a $p$-fraction of errors with list size $L$. Its cardinality meets the required $|C| = M \ge M$.

In both cases we have produced a code of size at least $M = \lfloor q^{rn}\rfloor$ that is $(p, L)$-list-decodable, which is the claim. $\blacksquare$

**Key facts.** `ErrorCorrectingCodes.Codeword.qary_entropy_pos`, `ErrorCorrectingCodes.Codeword.hamming_ball_size_asymptotic_upper_bound`, `ErrorCorrectingCodes.Codeword.listDecoding_counting_ineq`, `ErrorCorrectingCodes.Codeword.lt_one_of_le_one_sub_inv`, `ErrorCorrectingCodes.Codeword.exists_listDecodable_code`.
