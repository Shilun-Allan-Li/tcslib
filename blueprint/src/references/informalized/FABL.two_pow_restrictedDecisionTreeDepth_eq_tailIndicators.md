<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.two_pow_restrictedDecisionTreeDepth_eq_tailIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth from tail indicators

**Claim.** For a restricted Boolean function with decision tree depth $D$ on $n$ coordinates, if $I_k$ indicates whether $k\le D$, then $2^D=1+\sum_{j=0}^{n-1}2^j I_{j+1}$.

**Proof.** The restricted decision tree has depth at most $n$ (`restrictedDecisionTreeDepth_le_dimension`). For any natural depth $d\le N$, the binary expansion identity expresses $2^d$ as one plus the weighted sum of the indicators of the events $j+1\le d$, for $0\le j<N$ (`two_pow_eq_one_add_sum_tailIndicators`). Apply this identity with the restricted depth and dimension. Each such indicator is exactly the switching failure indicator at level $j+1$, by its definition, giving the stated formula.

**Key facts.** `FABL.restrictedDecisionTreeDepth_le_dimension`, `FABL.two_pow_eq_one_add_sum_tailIndicators`.
