<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.isEulerLiar_iff_emod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Remainder Characterization of Euler Liars

**Claim.** A natural number $A$ is an Euler liar for $N$ exactly when $\gcd(A,N)=1$ and the least nonnegative remainder of the Jacobi symbol $(A/N)$ modulo $N$ equals the remainder of $A^{(N-1)/2}$ modulo $N$.

**Proof.** Unfold the definition: the first condition is that $A$ and $N$ are coprime, and the second is equality in $\mathbb{Z}/N\mathbb{Z}$ between the Jacobi symbol and the indicated power of $A$. Regard the power as the natural-number power, cast first to the integers and then to $\mathbb{Z}/N\mathbb{Z}$; these casts agree with taking the power of the cast of $A$. Equality of two integer casts in $\mathbb{Z}/N\mathbb{Z}$ is equivalent to congruence modulo $N$. Taking the canonical remainders converts this congruence into the stated equality of remainders.
