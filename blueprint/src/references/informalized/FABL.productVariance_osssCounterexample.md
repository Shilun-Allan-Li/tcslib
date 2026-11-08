<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.productVariance_osssCounterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Counterexample Variance

**Claim.** For the second specified three-dimensional sign-cube function, with parameter $t=2+\sqrt{33}/3$, the uniform variance is $11/8+5\sqrt{33}/24$.

**Proof.** Under the uniform sign distribution, product variance equals ordinary uniform variance (FABL.productVariance_uniformSign). The variance of the displayed polynomial with parameter $t$ is $(3t^2-2t+3)/16$ (FABL.variance_osssCounterexampleAt). Substituting $t=2+\sqrt{33}/3$ and using $(\sqrt{33})^2=33$ gives $11/8+5\sqrt{33}/24$.

**Key facts.** `FABL.productVariance_uniformSign`, `FABL.variance_osssCounterexampleAt`.
