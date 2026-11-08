<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.signMultiIndexSupport_subsetMultiIndex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of a Subset Multi-Index

**Claim.** The support of the multi-index that is $1$ on $S$ and $0$ off $S$ is exactly $S$.

**Proof.** Check membership coordinate by coordinate. A coordinate lies in the support precisely when the corresponding multi-index value differs from zero. For the subset multi-index, that value is $1$ when the coordinate is in $S$ and $0$ otherwise; since $1\ne0$ in $\mathrm{Fin}(2)$, support membership is equivalent to membership in $S$. Thus the two finite sets are equal.
