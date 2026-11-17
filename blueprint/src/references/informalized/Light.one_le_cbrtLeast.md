<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.one_le_cbrtLeast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Least Cube Root

**Claim.** If $n\ge1$ and $r$ is the least natural number with $n\le r^3$, then $r\ge1$.

**Proof.** The defining property of the least cube root gives $n\le r^3$ (`Light.le_cbrtLeast_pow`). If $r$ were zero, this would imply $n\le0$, contradicting $n\ge1$. Thus $r\ge1$.

**Key facts.** `Light.le_cbrtLeast_pow`.
