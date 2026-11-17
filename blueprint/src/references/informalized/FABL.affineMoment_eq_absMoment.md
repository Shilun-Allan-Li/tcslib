<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.affineMoment_eq_absMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Moment as an Absolute Moment

**Claim.** If $1+ctX(x)>0$ for every $x$, then the average of $(1+ctX(x))^r$ equals the average of $|1+ctX(x)|^r$.

**Proof.** For each $x$, the assumed positivity gives $|1+ctX(x)|=1+ctX(x)$. Raising these equal quantities to the power $r$ preserves equality. Hence the summands in the two finite averages agree pointwise, so their averages are equal.
