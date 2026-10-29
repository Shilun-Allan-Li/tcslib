<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: LMN.cleanDNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Cleaning a DNF does not increase its width

**Claim.** Let $d$ be a DNF over $n$ variables: a list of terms, each term a list of literals. Its cleaned version is formed by deleting every contradictory term — one that contains some variable both positively and negatively — and then, within each surviving term, discarding any literal whose variable already occurred in an earlier retained literal. Writing $\mathrm{width}(t)$ for the number of literals in a term $t$ and $\mathrm{width}(d)$ for the largest width among the terms of $d$ (and $0$ when there are no terms), the claim is that the cleaned formula has width at most $\mathrm{width}(d)$.

**Proof.** Throughout, the width of a formula is computed by the function $M(\ell) = \mathrm{foldr}\ \max\ 0\ \ell$ applied to the list $\ell$ of the widths of its terms; this is the maximum of the entries of $\ell$, taken to be $0$ on the empty list. Deduplication within a term is performed by a map $\mathrm{dedup}$ that walks the term and keeps a literal only when no literal with the same variable has yet been retained, so it can only delete literals. The cleaned formula's term list is obtained by first filtering $d$'s terms down to the non-contradictory ones and then applying $\mathrm{dedup}$ to each survivor.

The proof reduces the inequality $\mathrm{width}(\mathrm{clean}(d)) \le \mathrm{width}(d)$ to the single structural fact that $\mathrm{dedup}$ never lengthens a term, using two elementary observations about $M$ that are re-derived in place (the function $M$ is defined ad hoc, so there is no library lemma to cite). Both are proved by induction on the list.

1. **$M$ is a least upper bound.** For lists $\ell_1,\ell_2$ of naturals, if every entry $x$ of $\ell_1$ satisfies $x \le M(\ell_2)$, then $M(\ell_1) \le M(\ell_2)$. Induction on $\ell_1$: the empty case gives $M([]) = 0$, which is below any bound; for $x :: \ell$ we have $M(x :: \ell) = \max\!\big(x, M(\ell)\big)$, and both arguments are $\le M(\ell_2)$ — the first by hypothesis, the second by the induction step — so their maximum is too.

2. **$M$ is an upper bound.** For a list $\ell$ of naturals, if $w \in \ell$ then $w \le M(\ell)$. Again by induction: if $w$ is the head then $w \le \max(w, M(\mathrm{tail})) = M(\ell)$; if $w$ lies in the tail then by induction $w \le M(\mathrm{tail}) \le M(\ell)$.

3. **Reduction via step 1.** The cleaned width is $M(L_{\mathrm{clean}})$, where $L_{\mathrm{clean}}$ is the list of widths of the cleaned terms, and $\mathrm{width}(d) = M(L_d)$, where $L_d$ is the list of widths of $d$'s terms. By step 1 it suffices to show that every entry of $L_{\mathrm{clean}}$ is $\le M(L_d) = \mathrm{width}(d)$.

4. **Locating a surviving term.** Fix an entry $x$ of $L_{\mathrm{clean}}$. By construction $L_{\mathrm{clean}}$ consists of the numbers $\mathrm{width}(\mathrm{dedup}(t))$ as $t$ ranges over the non-contradictory terms of $d$. Hence there is a term $t$ of $d$ that is not contradictory and with $x = \mathrm{width}(\mathrm{dedup}(t))$.

5. **Bounding that entry.** Deduplication does not increase the number of literals: $\mathrm{width}(\mathrm{dedup}(t)) \le \mathrm{width}(t)$ (this is the upstream fact `dedupTermVar_width_le`, that the deduplicated list is no longer than the original). Moreover $t$ is one of $d$'s terms, so $\mathrm{width}(t)$ occurs in the list $L_d$; by step 2, $\mathrm{width}(t) \le M(L_d) = \mathrm{width}(d)$. Chaining these,
\[
x = \mathrm{width}(\mathrm{dedup}(t)) \le \mathrm{width}(t) \le \mathrm{width}(d).
\]

Since the arbitrary entry $x$ of $L_{\mathrm{clean}}$ is bounded by $\mathrm{width}(d)$, step 1 yields $\mathrm{width}(\mathrm{clean}(d)) = M(L_{\mathrm{clean}}) \le \mathrm{width}(d)$, as required. Note that deleting contradictory terms plays no quantitative role here beyond shrinking the term list: it only removes entries from $L_{\mathrm{clean}}$, which can only lower a maximum, and the real work is the per-term bound of step 5.

**Key facts.** `LMN.dedupTermVar_width_le`.
