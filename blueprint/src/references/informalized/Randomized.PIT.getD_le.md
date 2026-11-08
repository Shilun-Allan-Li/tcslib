<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.getD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Defaulted List Entry

**Claim.** If every entry of $vs$ is less than $k$, then for each index $j$ its defaulted lookup $vs.getD\ j\ 0$ is at most $k$.

**Proof.** Express the defaulted lookup as lookup through the optional indexed element. If there is no entry at $j$, the result is the default $0$, which is at most $k$. If the entry is $v$, it belongs to the list, so the hypothesis gives $v<k$ and hence $v\le k$; the lookup is therefore at most $k$ in either case.
