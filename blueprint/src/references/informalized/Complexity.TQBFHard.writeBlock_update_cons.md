<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.writeBlock_update_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Written Bit

**Claim.** Writing $\beta$ starting at position $i+1$ after setting position $i$ to $b$ gives the same sequence as writing $b$ followed by $\beta$ starting at position $i$.

**Proof.** Compare the two resulting sequences at an arbitrary position $v$, splitting into $v<i$, $v=i$, and $v>i$. Before $i$, neither writing affects the position, and the point update at $i$ does not affect it either. At $i$, the longer block begins with $b$; on the other side, the block beginning at $i+1$ does not reach backward to $i$, so the point update supplies $b$. For $v>i$, write $v=i+1+j$ for some $j\ge0$. If $j<|\beta|$, both writes apply and select the same bit $\beta_j$: the offset from $i+1$ is $j$, and the offset from $i$ in the block $b::\beta$ is $j+1$. If $j\ge|\beta|$, neither block writes at $v$; the point update at $i$ is irrelevant there, so both sides equal $\sigma(v)$. Thus the sequences agree everywhere.
