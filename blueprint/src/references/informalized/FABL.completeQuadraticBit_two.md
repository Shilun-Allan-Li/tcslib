<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.completeQuadraticBit_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bit in two coordinates

**Claim.** For $a,b\in\mathbb{F}_2$, the complete quadratic bit of $(a,b)$ equals $ab$.

**Proof.** Use the full-sum formula for the complete quadratic bit ( `completeQuadraticBit_eq_full_sum`) and expand the sum over the two coordinates. The only pair with the first coordinate strictly less than the second is $(0,1)$; all other terms vanish. The surviving product is the value at coordinate $0$ times the value at coordinate $1$, namely $ab$.

**Key facts.** `FABL.completeQuadraticBit_eq_full_sum`.
