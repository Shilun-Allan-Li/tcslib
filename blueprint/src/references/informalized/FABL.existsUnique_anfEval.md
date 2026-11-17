<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.existsUnique_anfEval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique algebraic normal form

**Claim.** Every Boolean function on $\mathbb F_2^n$ has a unique coefficient family whose algebraic-normal-form evaluation equals that function.

**Proof.** The coefficient family $\operatorname{anfCoeff}(f)$ represents $f$, by the reconstruction identity `anfEval_anfCoeff`. For uniqueness, suppose another coefficient family $c$ also evaluates to $f$. Then the evaluations of $c$ and $\operatorname{anfCoeff}(f)$ agree. Injectivity of the evaluation map (`anfEval_injective`) forces the two coefficient families to be equal. Thus a representing family exists and is unique.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.anfEval_injective`.
