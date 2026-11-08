<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.booleanInfluence_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation Preserves Influence

**Claim.** Negating every output of a Boolean function leaves the probability that flipping a given coordinate changes its value unchanged.

**Proof.** Influence is the uniform average of the indicator of the event that the function changes under a coordinate flip. At each input, negating both values being compared preserves whether they are unequal: $-f(x)\ne -f(\mathrm{flip}_i(x))$ exactly when $f(x)\ne f(\mathrm{flip}_i(x))$. Thus the two pivotal-event indicators agree at every input, and so do their uniform averages.

**Key facts.** `FABL.isPivotal_neg_iff`.
