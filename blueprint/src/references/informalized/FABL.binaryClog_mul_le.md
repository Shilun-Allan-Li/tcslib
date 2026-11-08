<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.binaryClog_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Logarithm of a Product

**Claim.** For all natural numbers $a$ and $b$, $\operatorname{clog}_2(ab)\le \operatorname{clog}_2(a)+\operatorname{clog}_2(b)$, with the natural-number convention at zero.

**Proof.** For base $2$, the ceiling logarithm satisfies $n\le 2^{\operatorname{clog}_2(n)}$ for every natural number $n$. Applying this to $a$ and $b$ and multiplying yields $ab\le 2^{\operatorname{clog}_2(a)}2^{\operatorname{clog}_2(b)}=2^{\operatorname{clog}_2(a)+\operatorname{clog}_2(b)}$. The characterization of the ceiling logarithm by powers of $2$ then gives the claimed inequality. The base condition required for that characterization holds because $2>1$.
