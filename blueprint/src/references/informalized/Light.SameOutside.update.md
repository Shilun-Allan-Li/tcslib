<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SameOutside.update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating inside an interval

**Claim.** Replacing the value of $\mu'$ at an index inside $[a,a+n)$ preserves its agreement with $\mu$ outside that interval.

**Proof.** Fix an index $c$ outside $[a,a+n)$. The interior assumptions $a\le b$ and $b<a+n$ imply $b\ne c$: if $c<a$, then $b>c$, while if $a+n\le c$, then $b<c$. Since the update changes the sequence only at $b$, its value at $c$ remains $\mu'(c)$. The assumed agreement there therefore gives the required equality with $\mu(c)$.
