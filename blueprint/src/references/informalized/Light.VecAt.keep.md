<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.VecAt.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving a represented vector

**Claim.** If $\mu$ represents $I$ starting at index $a$, and $\mu'$ agrees with $\mu$ throughout the interval from $a$ to $a+t-1$, then $\mu'$ also represents $I$ starting at $a$.

**Proof.** Fix any $k$ with $k<t$. The index $a+k$ lies in the interval from $a$ to $a+t-1$, so the agreement hypothesis gives $\mu'(a+k)=\mu(a+k)$. Since $\mu$ represents $I$ starting at $a$, its value there is the natural-number value of $I(k)$. Thus $\mu'(a+k)$ has that same value, for every such $k$, which proves the representation claim.
