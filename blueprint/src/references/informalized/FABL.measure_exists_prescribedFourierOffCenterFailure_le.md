<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_exists_prescribedFourierOffCenterFailure_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Off-center Fourier failure bound

**Claim.** Under the stated size condition on the nonempty family $\mathcal F$ and for $0<\varepsilon<1$, a uniformly random sign-valued function has probability at most $2^{-n}$ of having some cube point where the prescribed off-center sum has absolute value at least $\varepsilon$.

**Proof.** Write the event that some point $x$ witnesses failure as the union, over all cube points $x$, of the events that the off-center sum at that particular point has absolute value at least $\varepsilon$. The finite union bound makes its probability at most the sum of the pointwise probabilities. By the pointwise estimate (`FABL.measure_prescribedFourierOffCenterSum_abs_ge_le`), each summand is at most $4^{-n}$. There are $2^n$ cube points, so the total is at most $2^n4^{-n}=2^{-n}$.

**Key facts.** `FABL.measure_prescribedFourierOffCenterSum_abs_ge_le`.
