<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_subset_pair_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a subset product

**Claim.** If the expectation of $g$ over two independent uniform signs is $c$, then the expectation of the product $\prod_{i\in S}g(x_i,y_i)$ over independent uniform sign vectors is $c^{|S|}$.

**Proof.** Regard each factor as indexed by every coordinate, using $g(x_i,y_i)$ when $i\in S$ and $1$ otherwise. Independence across coordinates makes the expectation of this product the product of the coordinatewise expectations (by `FABL.expect_pair_prod_finArrow`). For coordinates in $S$, that expectation is $c$ by hypothesis; outside $S$, it is $1$. The resulting product has one factor $c$ for each element of $S$, hence equals $c^{|S|}.

**Key facts.** `FABL.expect_pair_prod_finArrow`.
