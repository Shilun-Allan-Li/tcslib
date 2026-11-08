<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.not_isPmfTwoEvenHypercontractive_of_evenMoment_gt_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Necessary Even-Moment Bound

**Claim.** Under the stated moment hypotheses, if the $2j$-th moment exceeds the sharp bound, then the law and random variable are not $(2r,\rho)$-hypercontractive at the sharp noise parameter.

**Proof.** Assume, for contradiction, that the stated hypercontractivity property holds. The even-moment consequence of hypercontractivity (`evenMoment_le_sharp_of_hypercontractive`) then says that the $2j$-th moment is at most the sharp bound, using the given normalization, odd-moment vanishing, and preceding even-moment equalities. This contradicts the assumed strict inequality, so the hypercontractivity property fails.

**Key facts.** `FABL.evenMoment_le_sharp_of_hypercontractive`.
