<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values Within a Segment

**Claim.** For every index $i$ less than the length of $l$, the value $\mu(a+i)$ equals the $i$th entry of $l$.

**Proof.** By the definition of a segment, its values agree with the corresponding list entries at every index below the list's length. Applying this property to $i$ gives $\mu(a+i)=l_i$.
