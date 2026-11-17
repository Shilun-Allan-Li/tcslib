<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.restrictSubsetTo_liftSubsetFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction After Lifting a Subset

**Claim.** For a finite coordinate set $J$ and a subset $T$ of $J$, lifting $T$ to the ambient coordinate set and then restricting back to $J$ recovers $T$.

**Proof.** Check membership for an arbitrary element $j$ of $J$. Its ambient coordinate belongs to the lifted set exactly when it is the image of some element of $T$. Since lifting uses the inclusion of $J$ into the ambient set, that element must be $j$ itself. Thus $j$ belongs to the restricted set exactly when $j\in T$, proving equality.
