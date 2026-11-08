<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.mul_two_pow_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power threshold and round count

**Claim.** For natural numbers $a,M,i$ with $1\le M$, the inequality $M2^i\le a$ holds exactly when $i$ is less than the number of rounds $\mathrm{emodRounds}(a,M)=\mathrm{size}(a/M)$.

**Proof.** By the defining property of natural-number size, $i<\mathrm{size}(a/M)$ is equivalent to $2^i\le a/M$. Since $M$ is positive, the quotient inequality $2^i\le a/M$ is equivalent to $M\cdot 2^i\le a$. Commuting the factors gives the stated inequality and proves both directions.
