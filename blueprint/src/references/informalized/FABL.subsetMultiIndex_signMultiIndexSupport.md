<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.subsetMultiIndex_signMultiIndexSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support Recovers the Subset Index

**Claim.** For an index taking values in $\mathrm{Fin}(2)$, the subset index of its support equals the original index.

**Proof.** Evaluate both indices at an arbitrary coordinate. An element of $\mathrm{Fin}(2)$ is either $0$ or $1$. If the value is $0$, the coordinate is not in the support, and the subset index there is $0$. If the value is $1$, the coordinate is in the support, and the subset index there is $1$. Hence the indices agree at every coordinate.
