<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCursor_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Saturating Cursor Orbit

**Claim.** If each step sends $P(j)$ to $P(\min(j+1,R+1))$ for every $j\le R+1$, then iterating the step $i$ times from $P(0)$ gives $P(\min(i,R+1))$.

**Proof.** Induct on $i$. For $i=0$, zero iterations leave $P(0)$ unchanged. For the successor, the induction hypothesis identifies the current word as $P(\min(i,R+1))$. This index is at most $R+1$, so the assumed transition rule applies and sends it to $P(\min(\min(i,R+1)+1,R+1))$. This index equals $\min(i+1,R+1)$, proving the successor case.
