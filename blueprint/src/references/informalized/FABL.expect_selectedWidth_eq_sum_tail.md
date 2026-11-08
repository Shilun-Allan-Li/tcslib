<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.expect_selectedWidth_eq_sum_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected selected width from tail probabilities

**Claim.** The uniform expectation of the selected term's width equals the sum, for $k=0,\ldots,n-1$, of the probabilities that the width is at least $k+1$.

**Proof.** For each input $x$, express its selected width as the sum of the indicators of the events $k+1\le W(x)$ for $k$ in the range from $0$ to $n-1$. Indeed, the indices passing this threshold are exactly the first $W(x)$ indices: the selected width is at most $n$ (`selectedWidth_le_dimension`), and membership in the threshold set is equivalent to $k<W(x)$. Thus the number of such indices is $W(x)$. Taking expectations of this pointwise identity and interchanging the finite sum with expectation yields the sum of the expectations of these indicators. By the definition of uniform probability, each such expectation is the corresponding tail probability.

**Key facts.** `FABL.DNFFormula.selectedWidth_le_dimension`.
