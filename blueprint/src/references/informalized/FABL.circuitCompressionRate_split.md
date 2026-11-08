<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.circuitCompressionRate_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting the Compression Rate

**Claim.** When $1\le r$, multiplying the switching-layer rate at $w$ by the rate with both base indices $\ell$ and exponent $r-1$ gives the rate with indices $w,\ell$ and exponent $r$.

**Proof.** Since $r$ is positive, $r=(r-1)+1$. The power law therefore gives $s(\ell)^r=s(\ell)^{r-1}s(\ell)$. Expanding the two compression rates in the claimed identity, its left side is $s(w)\bigl(s(\ell)s(\ell)^{r-1}\bigr)$. By associativity and commutativity of multiplication this equals $s(w)\bigl(s(\ell)^{r-1}s(\ell)\bigr)$, which is $s(w)s(\ell)^r$, the right side.
