<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.exercise9_6_tensorPower_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment of an independent tensor power

**Claim.** For $d$ independent samples from a finite probability mass function $p$, the expectation of the $m$th power of the product of the values of $g$ is the $d$th power of the expectation of $g^m$ under $p$.

**Proof.** The $m$th power of the product $\prod_{i=1}^d g(x_i)$ equals $\prod_{i=1}^d g(x_i)^m$. Independence gives the expectation of this product as the product of the coordinate expectations (`pmfExpectation_independentProductPMF_prod`). Each coordinate has the same mass function $p$ and the same function $x\mapsto g(x)^m$, so each factor is $\mathbb E_{x\sim p}[g(x)^m]$. Their product is its $d$th power, as claimed.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`.
