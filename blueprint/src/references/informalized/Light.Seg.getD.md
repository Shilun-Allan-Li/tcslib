<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Defaulted Lookup Within a Segment

**Claim.** For every index $i<|l|$ and every integer $d$, the value $\mu(a+i)$ equals the lookup of $l$ at index $i$ with default $d$.

**Proof.** The segment property gives $\mu(a+i)=l_i$. Since $i$ is in range, the defaulted lookup equals the ordinary $i$th list entry. Combining these equalities proves the claim; the value of the default is immaterial in range.
