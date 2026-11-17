<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AverageInfluence.lean :: FABL.one_sub_inverse_dimension_pow_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for an Inverse-Dimension Power

**Claim.** For a positive natural number $n$ and any natural number $k$, $1-(1-2/n)^k\le2k/n$.

**Proof.** Regard $n$ as a positive real number. Since $n\ge1$, we have $2/n\le2$, so $-2/n\ge-2$. Bernoulli's inequality in the form $(1+ka)^k\le(1+a)^k$ for $a\ge-1$, equivalently $1+ka\le(1+a)^k$, applied with $a=-2/n$, gives $1-2k/n\le(1-2/n)^k$. Subtracting from $1$ yields the claimed upper bound.
