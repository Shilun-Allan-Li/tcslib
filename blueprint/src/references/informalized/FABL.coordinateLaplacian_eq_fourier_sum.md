<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.coordinateLaplacian_eq_fourier_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Laplacian Fourier Expansion

**Claim.** At each input, the coordinate Laplacian is the sum of the Fourier terms whose sets contain the chosen coordinate.

**Proof.** Expand $f(x)$ in its Fourier expansion and express its coordinate expectation as the sum of Fourier terms indexed by sets that do not contain $i$ (`FABL.fourier_expansion`, `FABL.coordinateExpectation_eq_fourier_sum`). The coordinate Laplacian is $f(x)$ minus that expectation (`FABL.coordinateLaplacian_apply`). Split the full Fourier sum into sets containing $i$ and sets not containing $i$. The latter terms cancel against the coordinate-expectation sum, leaving precisely the terms with $i\in S$.

**Key facts.** `FABL.coordinateLaplacian_apply`, `FABL.fourier_expansion`, `FABL.coordinateExpectation_eq_fourier_sum`.
