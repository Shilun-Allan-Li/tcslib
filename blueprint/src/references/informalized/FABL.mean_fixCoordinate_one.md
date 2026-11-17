<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_fixCoordinate_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean After Fixing a Coordinate

**Claim.** Fixing coordinate $i$ to $1$ changes the uniform mean of $f$ by its Fourier coefficient at $\{i\}$: the resulting mean is $\operatorname{mean}(f)+\widehat f(\{i\})$.

**Proof.** At each input, the value of $f$ with coordinate $i$ fixed to $1$ is the sum of the coordinate average and the discrete derivative in coordinate $i$: these are respectively the half-sum and half-difference of the two values obtained by setting that coordinate to $1$ and $-1$ (FABL.coordinateExpectation_apply; FABL.discreteDerivative_apply). Taking means splits this sum into the mean of the coordinate average and the mean of the derivative. The former equals the original mean (FABL.mean_coordinateExpectation), while the latter is the singleton Fourier coefficient (FABL.mean_discreteDerivative_eq_fourierCoeff_singleton).

**Key facts.** `FABL.coordinateExpectation_apply`, `FABL.discreteDerivative_apply`, `FABL.mean_discreteDerivative_eq_fourierCoeff_singleton`, `FABL.mean_coordinateExpectation`.
