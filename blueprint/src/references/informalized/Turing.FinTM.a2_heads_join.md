<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_heads_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combining Head Bounds Across Runs

**Claim.** If all configurations through time $a$ have work-tape heads in $[-B,B]$, and all configurations up to $b$ steps from the configuration at time $a$ have the same bound, then all configurations through time $a+b$ have that bound.

**Proof.** Fix $u\le a+b$. If $u\le a$, apply the first hypothesis. Otherwise write $u=a+(u-a)$. The run decomposition identity (`runFrom_add`) identifies the configuration at time $u$ with the configuration reached after $u-a$ steps from the configuration at time $a$. Since $u\le a+b$, we have $u-a\le b$, so the second hypothesis supplies the head bound.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
