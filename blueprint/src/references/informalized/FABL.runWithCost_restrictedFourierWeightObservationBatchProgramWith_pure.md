<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightObservationBatchProgramWith_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Observation Batch Output and Cost

**Claim.** For fixed input sequences and an initial list of rational observations, the batch program with a pure continuation deterministically returns the specified output list, at cost $(0,2m,m(2+2n+2|S|+1))$.

**Proof.** Induct on $m$, generalizing over the initial observation list. At $m=0$, the program passes the reversed initial list to the pure continuation, which returns it without cost; the claimed batch cost is also zero. At the successor step, the program makes two target queries and charges the prescribed work for the current observation. It prepends the computed product of restricted Fourier observations to the accumulator, then recurses on the three tail sequences. The induction hypothesis identifies the final list with the auxiliary output definition and supplies the remaining cost. Adding the two query costs and the current observation work yields the cost for $m+1$.
