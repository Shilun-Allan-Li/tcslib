<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.runWithCost_queriedFiniteFamilyFourierEstimatorFromInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queried finite-family estimator from inputs

**Claim.** For fixed inputs indexed by the finite family and sample positions, the queried estimator’s run is deterministic: it returns the finite-family Fourier estimate and has the specified inner cost.

**Proof.** The program first queries the target at each of the given inputs. The queried-batch run theorem identifies this phase with the deterministically labeled input sequence and cost $(0,m,m)$, where $m=|\mathcal F|$ times the number of samples. The continuation computes the empirical Fourier coefficients from those labeled samples and charges its prescribed additional work. The bind rule for run laws combines the two phases by adding their costs. Substituting the definitions of the output and inner cost gives the asserted point mass.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_queryInputBatchProgram`.
