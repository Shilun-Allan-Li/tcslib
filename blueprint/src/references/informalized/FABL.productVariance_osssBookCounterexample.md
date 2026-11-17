<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.productVariance_osssBookCounterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Counterexample Variance

**Claim.** For the first specified three-dimensional sign-cube function, with parameter $t=2+\sqrt{3}$, the uniform variance is $(20+10\sqrt{3})/16$.

**Proof.** Under the uniform sign distribution, product variance equals ordinary uniform variance (FABL.productVariance_uniformSign). The variance of the displayed polynomial with parameter $t$ is $(3t^2-2t+3)/16$ (FABL.variance_osssCounterexampleAt). Substituting $t=2+\sqrt{3}$ and using $(\sqrt{3})^2=3$ simplifies this expression to $(20+10\sqrt{3})/16$.

**Key facts.** `FABL.productVariance_uniformSign`, `FABL.variance_osssCounterexampleAt`.
