<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.hypercontractiveMomentGap_hasDerivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the moment gap

**Claim.** Under the stated pointwise positivity assumptions, the hypercontractive moment gap is differentiable at $t$, with derivative equal to its specified moment-gap derivative.

**Proof.** The pointwise positivity assumptions allow differentiation of each affine moment (FABL.affineMoment_hasDerivAt) and ensure that each affine moment is positive (FABL.affineMoment_pos). Positivity permits the real-power chain rule for raising the first moment to $q$ and the second to $p$. Subtracting the resulting derivatives gives precisely the specified hypercontractive moment-gap derivative.

**Key facts.** `FABL.affineMoment_hasDerivAt`, `FABL.affineMoment_pos`.
