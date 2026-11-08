<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.mean_nearlyConstantMinorityIndicator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minority Indicator Mean Bound

**Claim.** If \(1-\delta\le |\mathbb E f|\), then the uniform mean of the nearly constant minority indicator is at most \(\delta/2\).

**Proof.** The exact mean formula for the minority indicator (\(\texttt{FABL.mean_nearlyConstantMinorityIndicator}\)) identifies its mean with \((1-|\mathbb E f|)/2\). The hypothesis implies \(1-|\mathbb E f|\le\delta\); dividing by the positive number \(2\) gives the asserted bound.

**Key facts.** `FABL.mean_nearlyConstantMinorityIndicator`.
