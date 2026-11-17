<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightObservationProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of a Restricted Fourier Observation

**Claim.** The program that queries the target at the two cube points formed from $(y,z)$ and $(y',z)$ returns the product of the corresponding restricted Fourier observations, evaluated at the two target answers, and has cost $(0,2,2+2n+2|S|+1)$.

**Proof.** Unfold the program: it makes the first query at the point formed from $(y,z)$, then the second at the point formed from $(y',z)$. Each query supplies its target value and adds one query and one unit of work. The ensuing tick adds the prescribed observation work, and the pure return outputs exactly the product of the two rational Fourier observations with those answers. Thus the output is deterministic, with two queries and work $1+1+(2n+2|S|+1)$; adding the zero random-example count gives the stated cost.
