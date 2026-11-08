<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/StablePass.lean :: Light.keyAt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Key at a list index

**Claim.** For $j<|\pi|$, applying $kd$ to the entry of $\pi$ at index $j$ gives $kd(\pi_j)$.

**Proof.** By definition, the key at index $j$ is $kd$ applied to the defaulted lookup of $\pi$ at $j$. Since $j$ is in range, the defaulted lookup equals the indexed entry. Applying $kd$ to both sides gives the result.
