<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.expect_monomial_pairwiseVotes_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Monomial Average

**Claim.** For distinct pairwise contests $a,b$ and coordinate sets $S,T$, the average over independent uniform rankings is $(-1/3)^{|S|}$ if $S=T$, and $0$ otherwise.

**Proof.** For each coordinate $i$, combine its contributions to the two monomials into one factor: it is the product of the $a$-vote sign when $i\in S$ and the $b$-vote sign when $i\in T$, with a missing contribution treated as $1$. The product of these factors over coordinates is exactly the product of the two monomials. Since rankings at different coordinates are independent and uniform, the expectation of this product factors into the product of the coordinate expectations (`expect_rankingProfile_prod`). If $i$ lies in both sets, the coordinate expectation is $-1/3$ by the pairwise-vote correlation identity (`expect_rankingPreference_mul`). If it lies in exactly one set, the expectation is $0$ because each contest’s vote is unbiased (`expect_rankingPreference`); if in neither, it is $1$. When $S=T$, multiplying the factors gives $(-1/3)^{|S|}$. When $S\ne T$, some coordinate belongs to exactly one of the two sets, so its factor is zero and hence the whole product is zero.

**Key facts.** `FABL.expect_rankingProfile_prod`, `FABL.expect_rankingPreference_mul`, `FABL.expect_rankingPreference`.

**Caveat.** The supplied informal statement describes a different NAE and noise-stability identity; this account follows the formal statement and proof source, which establish the monomial-average formula.
