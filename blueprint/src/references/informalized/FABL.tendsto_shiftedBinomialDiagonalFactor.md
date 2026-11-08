<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_shiftedBinomialDiagonalFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Diagonal Factor Limit

**Claim.** For each natural number $c$, the sequence $(2m+c+1)/(2(m+c+1))$ tends to $1$ as $m\to\infty$.

**Proof.** A standard limit for affine functions of a variable tending to infinity states that $(am+b)/(cm+d)$ tends to $a/c$ when $c\ne0$. Here the coefficients of $m$ are both $2$, so the limit is $1$. Expanding the natural-number expressions in the numerator and denominator into this affine form identifies the given sequence with that quotient.
