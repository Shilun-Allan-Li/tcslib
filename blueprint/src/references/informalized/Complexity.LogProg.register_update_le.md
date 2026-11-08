<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.register_update_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Update Preserves a Bound

**Claim.** If every register value is at most $B$ and $n\le B$, then updating register $r$ to $n$ leaves every register value at most $B$.

**Proof.** Fix a register $s$. If $s=r$, the updated value is $n$, which is at most $B$ by hypothesis. If $s\ne r$, the update leaves its value equal to $v(s)$, which is at most $B$ by the assumed bound on all register values.
