<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.ReedMuller_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Reed–Muller codes

**Claim.** Every Boolean function in $\mathrm{RM}(d,n)$ also belongs to $\mathrm{RM}(d+1,n)$; thus the Reed–Muller codes are nested as the degree bound increases by one.

**Proof.** Take any function in $\mathrm{RM}(d,n)$. Its membership gives the degree-at-most-$d$ condition on its sign-valued lift. The degree-successor theorem says that this condition implies the degree-at-most-$(d+1)$ condition for the same lift (`LowDegreeTest.degree_le_succ`). By the definition of Reed–Muller membership, the function therefore lies in $\mathrm{RM}(d+1,n)$.

**Key facts.** `LowDegreeTest.degree_le_succ`.
