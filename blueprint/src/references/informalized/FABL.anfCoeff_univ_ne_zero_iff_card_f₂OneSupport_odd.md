<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.anfCoeff_univ_ne_zero_iff_card_f₂OneSupport_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity of the one-set

**Claim.** The coefficient indexed by the full set is nonzero exactly when $f$ takes the value $1$ on an odd number of inputs.

**Proof.** The full-set coefficient equals the cardinality of the one-set, viewed as an element of $\mathbb F_2$ (by the full-set coefficient and one-set cardinality identity, `FABL.anfCoeff_univ_eq_card_f₂OneSupport`). In $\mathbb F_2$, the natural-number cast of a cardinality is nonzero precisely when that cardinality is odd. Applying this parity criterion gives the equivalence.

**Key facts.** `FABL.anfCoeff_univ_eq_card_f₂OneSupport`.
