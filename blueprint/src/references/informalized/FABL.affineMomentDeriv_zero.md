<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.affineMomentDeriv_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Moment Derivative at Zero

**Claim.** At $t=0$, the affine moment derivative equals $rc$ times the average of $X$.

**Proof.** Expand the finite average as a sum divided by the cardinality of the sample space. At zero, each base $1+ctX(x)$ is $1$, so its power is $1$ and the summand becomes $rcX(x)$. Pulling the constant $rc$ out of the sum gives $rc$ times the average of $X$, as claimed.
