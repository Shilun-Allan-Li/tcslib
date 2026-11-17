<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_carry_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant for Multiplication Carries

**Claim.** For bit strings $a,b$ and every natural number $n$, the weighted sum of the first $n$ product-column values equals the weighted sum of the first $n$ carry-determined output bits plus $2^n$ times the carry after column $n$.

**Proof.** Induct on $n$. For $n=0$, both sums are empty and the initial carry is zero. For the successor step, expand each sum by its term at column $n$ and use the induction hypothesis for the earlier columns. The recurrence defines the next carry as the quotient of the incoming carry plus the column value upon division by two. The quotient-remainder identity writes that total as twice the next carry plus its remainder modulo two. Multiplying this identity by $2^n$ shows that the new column contribution and the previous weighted carry combine into the new parity term and $2^{n+1}$ times the next carry, proving the invariant.
