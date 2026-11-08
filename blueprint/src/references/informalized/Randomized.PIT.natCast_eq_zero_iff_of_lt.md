<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.natCast_eq_zero_iff_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing of a natural residue

**Claim.** If $v<k$, then the residue of $v$ in $\mathbb Z/k\mathbb Z$ is zero exactly when $v=0$.

**Proof.** A natural number represents zero in $\mathbb Z/k\mathbb Z$ exactly when it is divisible by $k$. Thus, if the residue of $v$ is zero, $k$ divides $v$; since $v<k$, the only possibility is $v=0$. Conversely, zero is divisible by every natural number, so $v=0$ implies its residue is zero.
