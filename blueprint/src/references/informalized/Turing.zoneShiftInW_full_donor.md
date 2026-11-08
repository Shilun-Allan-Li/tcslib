<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneShiftInW_full_donor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inward Shift with an Empty Donor

**Claim.** If $1\le i<\ell$ and the word in zone $i-1$ is empty, then after shifting inward at level $i$, zone $i-1$ contains the first $2^{i-1}$ entries of the original word in zone $i$, while zone $i$ contains the remainder.

**Proof.** The level hypotheses make the inward shift active, and the empty-donor hypothesis selects its transfer branch. Since $i$ and $i-1$ are distinct, the two specified indices select the lower-zone and upper-zone clauses, respectively. Thus the lower zone receives the prefix of length $2^{i-1}$, and the upper zone receives the corresponding suffix, as claimed.
