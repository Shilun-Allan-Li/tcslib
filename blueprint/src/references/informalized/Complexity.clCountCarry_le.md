<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountCarry_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Carry Count Bound

**Claim.** For every finite Boolean word $w$, the number of its initial consecutive true bits is at most its length.

**Proof.** Proceed by induction on $w$. The empty word has carry count and length both zero. For a word $b::w$, if $b$ is false, its carry count is zero and the inequality is immediate. If $b$ is true, its carry count is one plus the carry count of $w$; the induction hypothesis bounds this by $1+w.length$, which is exactly the length of $b::w$.
