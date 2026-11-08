<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_nat_of_even_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence from parity subsequences

**Claim.** If both subsequences $f(2m)$ and $f(2m+1)$ tend to $L$, then $f(n)$ tends to $L$.

**Proof.** Fix $\varepsilon>0$. Convergence of the even and odd subsequences gives thresholds beyond which each is within $\varepsilon$ of $L$. Choose an index larger than twice the larger threshold. Every natural number beyond it is either even, of the form $2m$, or odd, of the form $2m+1$. In the corresponding case the index $m$ is beyond that subsequence's threshold, so $f(n)$ is within $\varepsilon$ of $L$. This is precisely convergence of the full sequence.
