<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.anfCoeff_affineFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# ANF coefficients of affine functions

**Claim.** For $b\in\mathbb F_2$ and $a\in\mathbb F_2^n$, the coefficient function of $x\mapsto b+a\cdot x$ has value $b$ on the empty set, value $\sum_{i\in S}a_i$ on singleton sets $S$, and value $0$ on all other sets.

**Proof.** Compare the proposed coefficient function with the actual coefficients by evaluating them: evaluation is injective (`FABL.anfEval_injective`). The evaluation of the actual coefficients recovers the affine function (`FABL.anfEval_anfCoeff`), while the evaluation of the stated affine coefficient formula is that same affine function (`FABL.anfEval_affineCoefficients`). Their evaluations agree, so the coefficient functions are equal.

**Key facts.** `FABL.anfEval_injective`, `FABL.anfEval_anfCoeff`, `FABL.anfEval_affineCoefficients`.
