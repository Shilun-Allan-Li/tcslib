<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: ErrorCorrectingCodes.Codeword.exists_listDecodable_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Existence of list-decodable codes by counting

**Claim.** Let $\alpha$ be a finite field and write $N = |\alpha|^n$ for the number of words in the space $\alpha^n$. Fix $n, L, M \in \mathbb{N}$ and $p \in [0,1]$ with $1 \le L$, $L < M$ and $M \le N$. Suppose $V \in \mathbb{N}$ bounds the volume of every Hamming ball of radius $\lfloor pn\rfloor$ — that is, for every center $y \in \alpha^n$ the ball $B(y) := \{\,x : d(x,y) \le \lfloor pn\rfloor\,\}$ has $|B(y)| \le V$ — and that
\[
N \cdot \binom{V}{L+1} \cdot \binom{N-(L+1)}{\,M-(L+1)\,} \;<\; \binom{N}{M}.
\]
Then there is a code $C \subseteq \alpha^n$ with exactly $M$ codewords that is $(p,L)$-list-decodable: for every $y \in \alpha^n$ one has $|B(y) \cap C| \le L$.

**Proof.** The proof is a counting argument run through the contrapositive, exactly as in the probabilistic method: rather than exhibit a good code, it shows that the bad codes are too few to exhaust all $M$-subsets.

Throughout write $N = |\alpha|^n$ (the cardinality of $\alpha^n$, computed from the product structure) and $B(y)$ for the Hamming ball of radius $\lfloor pn\rfloor$ about $y$.

1. **Contrapositive.** It suffices to prove
\[
\binom{N}{M} \;\le\; N \cdot \binom{V}{L+1} \cdot \binom{N-(L+1)}{M-(L+1)}
\]
under the assumption that *no* $M$-element code is $(p,L)$-list-decodable. Indeed, this is the negation of the displayed strict inequality, and the negation of the conclusion is precisely the assumption just stated.

2. **What failure means.** Unfolding list-decodability, a code $C$ fails to be $(p,L)$-list-decodable exactly when there is a center $y$ with $|B(y)\cap C| \ge L+1$. Call such a $C$ *bad for $y$*. The standing assumption thus says: every $M$-subset of $\alpha^n$ is bad for at least one center $y$.

3. **Counting the codes bad for a fixed center.** Fix $y$. We bound the number of $M$-subsets $C$ with $|B(y)\cap C| \ge L+1$. Any such $C$ can be described (not uniquely — we only need an upper bound) as follows: since $B(y)\cap C$ has at least $L+1$ elements, choose a subset $S \subseteq B(y)\cap C$ with $|S| = L+1$ (`Finset.exists_subset_card_eq`); then $S \subseteq B(y)$, $S \subseteq C$, and $C = S \cup (C\setminus S)$, where $T := C\setminus S$ is an $(M-(L+1))$-subset of the complement $\alpha^n\setminus S$. Hence $C$ lies in the image of the map $(S,T)\mapsto S\cup T$ as $S$ ranges over the $(L+1)$-subsets of $B(y)$ and $T$ over the $(M-(L+1))$-subsets of $\alpha^n\setminus S$. Since these images cover every code bad for $y$, the count of such codes is at most the number of pairs $(S,T)$ (`Finset.card_biUnion_le` for the union over $S$, `Finset.card_image_le` for each image, `Finset.card_sdiff` to compute $|\alpha^n\setminus S| = N-(L+1)$):
\[
\#\{C \text{ bad for } y\} \;\le\; \binom{|B(y)|}{L+1}\cdot\binom{N-(L+1)}{M-(L+1)}.
\]
Finally $|B(y)| \le V$ by the volume hypothesis, and the binomial coefficient is monotone in its upper argument (`Nat.choose_le_choose`), so
\[
\#\{C \text{ bad for } y\} \;\le\; \binom{V}{L+1}\cdot\binom{N-(L+1)}{M-(L+1)}.
\]
(The counts of $(L+1)$- and $(M-(L+1))$-subsets are read off from `Finset.card_powersetCard`.)

4. **Union bound over centers.** A code is bad iff it is bad for *some* $y$, so the set of bad $M$-subsets is contained in the union, over all $y\in\alpha^n$, of the sets in Step 3. There are exactly $N$ centers, so summing the bound of Step 3 over all $y$ (again `Finset.card_biUnion_le`) gives
\[
\#\{\text{bad } M\text{-subsets}\} \;\le\; N\cdot \binom{V}{L+1}\cdot\binom{N-(L+1)}{M-(L+1)}.
\]

5. **Every code is bad.** By the assumption of Step 2, *every* $M$-subset of $\alpha^n$ is bad, so the set of bad $M$-subsets is the whole collection of $M$-subsets, which has cardinality $\binom{N}{M}$ (`Finset.card_powersetCard`, with $|\alpha^n| = N$). Substituting this into Step 4 yields
\[
\binom{N}{M} \;\le\; N\cdot \binom{V}{L+1}\cdot\binom{N-(L+1)}{M-(L+1)},
\]
which is exactly the inequality required in Step 1. This completes the contrapositive, and with it the proof. $\qquad\blacksquare$
