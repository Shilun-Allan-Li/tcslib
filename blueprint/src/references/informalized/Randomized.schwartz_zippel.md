<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SchwartzZippel.lean :: Randomized.schwartz_zippel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Schwartz–Zippel Bound

**Claim.** For a nonzero integer polynomial in $m$ variables of total degree at most $d$, and a finite nonempty set $S$ of integers, the fraction of tuples in $S^m$ where the polynomial is nonzero is at least $1-d/|S|$.

**Proof.** The Schwartz–Zippel theorem bounds the fraction of tuples in $S^m$ where the polynomial vanishes by its total degree divided by $|S|$; applying it with the degree bound $d$ gives an upper bound of $d/|S|$ on that fraction. The set $S$ is nonempty, so the denominator $|S|^m$ is positive. Within the product set $S^m$, each tuple either is a zero or is a nonzero evaluation. Their counts therefore add to $|S|^m$. Dividing this count identity by the positive total and subtracting the zero fraction from $1$ gives the claimed lower bound for the nonzero fraction.
