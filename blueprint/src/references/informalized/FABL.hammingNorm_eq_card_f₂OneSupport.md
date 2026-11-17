<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.hammingNorm_eq_card_f₂OneSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hamming norm and support size

**Claim.** For every function $f:\mathbb F_2^n\to\mathbb F_2$, its Hamming norm equals the number of inputs $x$ for which $f(x)=1$.

**Proof.** The Hamming norm counts inputs at which $f$ is nonzero, while the one-support counts inputs at which $f(x)=1$. In $\mathbb F_2$, every value is either $0$ or $1$: a nonzero value must be $1$, and the value $0$ is not $1$. Thus the two counted sets coincide, and their cardinalities are equal.
