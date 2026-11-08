<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Braverman_Bound_Helper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling bound for the Braverman parameter

**Claim.** For $B=\log(m/varepsilon)+2$ and $k=\lceil B^{cd}\rceil$, under the stated hypotheses one has $k\le B^{(c+1)d}$.

**Proof.** If $d=0$, both powers are $1$, so the ceiling is $1$ and the inequality holds. Suppose $d=d_0+1$. Since $m/\varepsilon\ge1$, we have $\log(m/\varepsilon)\ge0$, hence $B\ge2$. The ceiling estimate gives $k<B^{c(d_0+1)}+1$. As $B^{c(d_0+1)}\ge1$, this is at most $2B^{c(d_0+1)}$. Also $B\ge2$, so $2\le B^{d_0+1}$. Multiplying these bounds yields $k\le B^{c(d_0+1)+d_0+1}=B^{(c+1)(d_0+1)}$, as required.
