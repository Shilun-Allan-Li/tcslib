<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.isPmfTwoEvenHypercontractive_iff_of_momentConditions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment characterization of hypercontractivity

**Claim.** Under the stated moment assumptions, the $2$-to-$2r$ hypercontractive inequality holds for all real $a,b$ exactly when $\rho\le 1/\sqrt{2r-1}$.

**Proof.** For necessity, the hypercontractive inequality and the normalization and vanishing odd moments give the necessary squared bound $\rho^2\le 1/(2r-1)$ (FABL.isPmfTwoEvenHypercontractive_necessary_sq). Since $\rho\ge0$ and $r>0$, taking square roots yields the claimed upper bound on $\rho$. For sufficiency, the assumed bound on $\rho$ gives $\rho^2\le 1/(2r-1)$. The moment-condition sufficiency theorem then supplies the hypercontractive inequality for all $a,b$ (FABL.isPmfTwoEvenHypercontractive_of_momentConditions). These implications establish the equivalence.

**Key facts.** `FABL.isPmfTwoEvenHypercontractive_necessary_sq`, `FABL.isPmfTwoEvenHypercontractive_of_momentConditions`.
