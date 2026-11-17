<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sq_card_inter_eq_sum_pairIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intersection Cardinality as a Pair Count

**Claim.** For finite coordinate sets $U,J\subseteq\{1,\ldots,n\}$, $|U\cap J|^2$ equals the sum over ordered pairs $(i,j)\in U\times U$ of the indicator that both coordinates belong to $J$.

**Proof.** The intersection cardinality is the sum over $i\in U$ of the indicator of $i\in J$ (the counting identity `card_inter_eq_sum_memIndicator`). Squaring this sum and expanding it as a product of two finite sums gives a sum over ordered pairs $(i,j)\in U\times U$. Each summand is the product of the two indicators, which is $1$ exactly when both $i$ and $j$ lie in $J$, and is $0$ otherwise. This is the asserted pair count.

**Key facts.** `FABL.card_inter_eq_sum_memIndicator`.
