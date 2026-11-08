<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_product_pm1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign-valued Gowers products

**Claim.** Every Gowers product of the sign lift of a Boolean function is either $1$ or $-1$.

**Proof.** First, each value of the sign lift is either $1$ or $-1$, directly from its definition. Induct on the order $k$, keeping the base point arbitrary. At order zero, the Gowers product is the sign lift itself, so the assertion follows. At order $k+1$, the recursive formula expresses the product as the product of two order-$k$ Gowers products, one at the original base point and one shifted by the last direction. By induction, each factor is in $\{1,-1\}$, and their product is again in $\{1,-1\}.

**Key facts.** `LowDegreeTest.gowers_product_succ`.
