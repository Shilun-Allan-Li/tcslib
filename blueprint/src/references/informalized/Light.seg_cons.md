<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.seg_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Segments of cons lists

**Claim.** The values of $\mu$ starting at index $a$ agree with $x::l$ if and only if $\mu(a)=x$ and the values starting at index $a+1$ agree with $l$.

**Proof.** If the segment agrees with $x::l$, its value at index $0$ gives $\mu(a)=x$. At a later index $i+1$, the entry of the cons list is the $i$th entry of $l$, and the memory address is $a+(i+1)=(a+1)+i$. This yields agreement with $l$ starting at $a+1$. Conversely, assume the value at $a$ is $x$ and the shifted segment agrees with $l$. The index-zero entry of the cons list is handled by the first equality. Every successor index $i+1$ is handled by the agreement for $l$ at index $i$, since the corresponding address is $(a+1)+i$. Thus the full segment agrees with the cons list.
