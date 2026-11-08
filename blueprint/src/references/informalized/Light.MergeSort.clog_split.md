<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.clog_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling Logarithm Under a Split

**Claim.** For every natural number $n\ge2$, the sum of the two split sizes times their ceiling base-two logarithms, plus $n$, is at most $n\operatorname{clog}_2(n)$.

**Proof.** Write $h=\lfloor(n+1)/2\rfloor$. For $n\ge2$, the ceiling-logarithm recurrence gives $\operatorname{clog}_2(n)=\operatorname{clog}_2(h)+1$. Also $n-h\le h$, so monotonicity of the ceiling logarithm gives $\operatorname{clog}_2(n-h)\le\operatorname{clog}_2(h)$. Let $c=\operatorname{clog}_2(h)$. Replacing the logarithm of the second part by the upper bound $c$ bounds its contribution by $(n-h)c$. The two weighted contributions are therefore at most $hc+(n-h)c=nc$. Adding $n$ gives $n(c+1)=n\operatorname{clog}_2(n)$, as required.
