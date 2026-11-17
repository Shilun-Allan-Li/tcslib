<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfInner_self_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Definiteness of the Probability Inner Product

**Claim.** If $\pi$ assigns positive mass to every point of the finite set, then $\langle f,f\rangle_\pi=0$ exactly when $f$ is identically zero.

**Proof.** Rewrite the inner product as the expectation of the pointwise square (`pmfInner_eq_expect`). For the forward direction, this expectation is a finite sum of nonnegative terms $(\pi(y))_{\mathbb R}f(y)^2$. A zero sum of nonnegative terms has every term equal to zero. At each point $x$, full support gives $(\pi(x))_{\mathbb R}>0$ (`PMFHasFullSupport.toReal_pos`), so the vanishing of its weighted square forces $f(x)^2=0$, hence $f(x)=0$. Since this holds for every $x$, $f$ is identically zero. Conversely, if $f$ is identically zero, its pointwise square is the constant zero function, whose expectation is zero (`pmfExpectation_const`); therefore the inner product vanishes.

**Key facts.** `FABL.pmfInner_eq_expect`, `FABL.PMFHasFullSupport.toReal_pos`, `FABL.pmfExpectation_const`.
