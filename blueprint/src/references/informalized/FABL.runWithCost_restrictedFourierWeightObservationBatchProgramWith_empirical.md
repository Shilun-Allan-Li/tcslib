<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightObservationBatchProgramWith_empirical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Observation Batch Run

**Claim.** For fixed input sequences and initial observations, the batch program followed by the finishing step returns the empirical restricted Fourier weight, with denominator $q$, of the resulting observation list, at cost $(0,2m,m(2+2n+2|S|+1)+(q+1))$.

**Proof.** Induct on the batch length $m$, generalizing over the initial observation list. At length zero, the program returns the reversed initial list to the finishing step, which computes its empirical weight with denominator $q$; the finishing step adds $q+1$ units of work and no queries. For the successor case, the program queries the target at each of the two inputs formed from the current split coordinates, so these queries contribute two query units. It records the product of the corresponding restricted Fourier observations, charges the prescribed observation work, and recurses on the three tails with this new observation prepended to the accumulator. The induction hypothesis gives the output from precisely this updated list and accounts for the remaining queries and work. Adding the two query charges and one observation-work charge gives the cost formula at length $m+1$; the arithmetic uses the recurrence for $(m+1)(2+\mathrm{work}(J,S))$.
