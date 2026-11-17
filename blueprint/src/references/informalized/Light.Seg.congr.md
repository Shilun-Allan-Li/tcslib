<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement preserves a segment

**Claim.** If $\mu$ agrees with a list throughout a segment and $\mu'$ agrees with $\mu$ at every index of that segment, then $\mu'$ agrees with the same list throughout it.

**Proof.** Take any position $i$ within the list. By hypothesis, $\mu'(a+i)=\mu(a+i)$, and the segment condition gives $\mu(a+i)=l[i]$. Transitivity of equality yields $\mu'(a+i)=l[i]$, as required.
