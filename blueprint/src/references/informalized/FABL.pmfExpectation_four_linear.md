<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_four_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of finite probability expectation

**Claim.** For real scalars $a,b,c,d$ and functions $f,g,h,k$ on a finite probability space, the expectation of $af+bg+ch+dk$ is $a\mathbb{E}_{\pi}[f]+b\mathbb{E}_{\pi}[g]+c\mathbb{E}_{\pi}[h]+d\mathbb{E}_{\pi}[k]$.

**Proof.** First regroup the pointwise linear combination as the sum of the four functions $af$, $bg$, $ch$, and $dk$; the expressions agree by associativity and commutativity of real addition and multiplication. Additivity of expectation splits the expectation of these sums into the sum of the four expectations. Pulling each constant scalar out of its expectation gives the stated formula.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const_mul`.
