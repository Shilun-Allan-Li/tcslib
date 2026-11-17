<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Odometer.lean :: Light.lt_of_mem_digitsLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base-digit bound

**Claim.** If $b>0$, every entry of the digit list for $b,n,c$ is less than $b$.

**Proof.** Membership in the mapped list means the entry has the form $c/b^k\bmod b$ for some position $k$. The remainder of any natural number modulo a positive modulus is strictly less than that modulus. Applying this remainder bound with modulus $b$ proves the claim.
