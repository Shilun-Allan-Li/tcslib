<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: RestrictionFourier.bernoulliRestrProb_card_inter_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# A random restriction keeps $k$ free coordinates in $U$ with probability at least $1/4$

**Claim.** Fix $n$ and a parameter $p \in [0,1]$, let $U \subseteq \mathrm{Fin}\,n$ be a set of coordinates, and let $k \ge 1$ be an integer with $3k \le p\,\lvert U\rvert$. Draw a Bernoulli($p$) random restriction $\rho$ on $n$ variables and let $J$ be its set of free variables. Then the chance that $U$ contains at least $k$ free coordinates is at least one quarter:
\[
  \Pr\bigl[\,k \le \lvert U \cap J\rvert\,\bigr] \;\ge\; \frac14.
\]

**Proof.** The argument simply passes to the complementary "few free coordinates" event, whose probability has already been bounded above, and then feeds in $k \ge 1$. Write $N := \lvert U \cap J\rvert$ for the number of free coordinates lying inside $U$.

1. **Pass to the complement.** The event $\{k \le N\}$ is precisely the negation of the event $\{N < k\}$. Since the Bernoulli weights $p^{\lvert J\rvert}\bigl((1-p)/2\bigr)^{\,n-\lvert J\rvert}$ form a probability distribution over restrictions when $0 \le p \le 1$, the probability of a negated event is one minus the probability of the event (complement rule, `bernoulliRestrProb_not`). Hence
\[
  \Pr[\,k \le N\,] \;=\; 1 - \Pr[\,N < k\,].
\]
(The only bookkeeping here is recognising $k \le N$ and $N < k$ as negations of one another.)

2. **Insert the tail bound.** The companion upper bound on the "few free coordinates" tail (`bernoulliRestrProb_card_inter_lt`), valid under the same hypotheses $0 \le p \le 1$, $k \ge 1$ and $3k \le p\,\lvert U\rvert$, gives
\[
  \Pr[\,N < k\,] \;\le\; \frac{3}{4k}.
\]
This is where the quantitative assumption $3k \le p\,\lvert U\rvert$ is spent; the present proof only transmits it to that lemma.

3. **Use $k \ge 1$ to simplify the bound.** Because $k \ge 1$ we have $4k \ge 4$, and therefore
\[
  \frac{3}{4k} \;\le\; \frac34 .
\]

4. **Combine.** Substituting the bounds of Steps 2 and 3 into the identity of Step 1,
\[
  \Pr[\,k \le N\,] \;=\; 1 - \Pr[\,N < k\,] \;\ge\; 1 - \frac{3}{4k} \;\ge\; 1 - \frac34 \;=\; \frac14,
\]
which is the claimed lower bound.

**Key facts.** `RestrictionFourier.bernoulliRestrProb_not`, `RestrictionFourier.bernoulliRestrProb_card_inter_lt`.
