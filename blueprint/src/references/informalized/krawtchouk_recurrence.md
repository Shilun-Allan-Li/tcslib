<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchouk_recurrence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk three-term recurrence

**Claim.** For $1\le j$, $j+1\le n$, and $x\le n$, the Krawtchouk polynomials satisfy the stated three-term recurrence.

**Proof.** Let $G(z)=\sum_{q=0}^{n}K_q(x)z^q=(1-z)^x(1+z)^{n-x}$, using the generating-function identity. Differentiating this product and simplifying gives the differential identity $(1-z^2)G'(z)=((n-2x)-nz)G(z)$. Substitute the finite polynomial expansion for $G$ and its derivative, then compare coefficients of $z^j$. The contributions from $G'$ and $z^2G'$ involve respectively the coefficients $K_{j+1}(x)$ and $K_{j-1}(x)$, while the right side contributes $(n-2x)K_j(x)-nK_{j-1}(x)$. Collecting these terms yields $(j+1)K_{j+1}(x)=(n-2x)K_j(x)-(n-j+1)K_{j-1}(x)$, as claimed.

**Key facts.** `krawtchouk_generating_function`.
