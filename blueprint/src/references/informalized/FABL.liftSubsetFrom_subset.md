<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.liftSubsetFrom_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted subset containment

**Claim.** Lifting a finite subset of the elements of $J$ back into the ambient set gives a subset of $J$.

**Proof.** Take any element of the lifted set. By the definition of lifting a finite set, it is the image under the subtype inclusion of some element of $T$. That subtype element belongs to $J$ by its defining membership condition, so its image lies in $J$.
