<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_digits_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of binary digits

**Claim.** If two length-$n$ sequences of digits in $\{0,1\}$ have equal weighted sums after adding $2^n k$ to the first, then $k=0$ and the digits agree at every position below $n$.

**Proof.** Induct on $n$. For $n=0$, both finite sums are empty, so the assumed equality immediately gives $k=0`, and there are no digits to compare. For the successor case, separate the zeroth terms from both sums. The equality becomes an equality of the zeroth digits plus twice the corresponding tail sums, with the carry term also absorbed inside the factor of two. Since each zeroth digit is either zero or one, equality forces $f(0)=g(0)$. Cancelling this common term and dividing the remaining equality by two gives the same hypothesis for the tail sequences $j\mapsto f(j+1)$ and $j\mapsto g(j+1)$, still with carry $k$. Apply the induction hypothesis: it gives $k=0$ and equality of all tail digits. Together with equality at position zero, this proves the claim.
