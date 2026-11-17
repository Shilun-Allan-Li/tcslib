<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.scanPre_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a Paired Encoding

**Claim.** For bit strings $\alpha$ and $w$, scanning their paired encoding retains the doubled encoding of $\alpha$ and the delimiter $[\mathrm{false},\mathrm{true}]$, stopping before $w$.

**Proof.** Induct on $\alpha$. When $\alpha$ is empty, the encoding begins with the unequal delimiter pair $[\mathrm{false},\mathrm{true}]$, which the scan retains and at which it stops. For $\alpha=b::\alpha'$, the encoding begins with the equal pair $[b,b]$. The scan retains this pair and continues on the remaining encoding. Apply the induction hypothesis to that remainder; joining its result to the retained pair gives the doubled encoding of all of $\alpha$ followed by the delimiter.

**Caveat.** The supplied informal statement is corrupted; the claim is read from the formal statement and proof.
