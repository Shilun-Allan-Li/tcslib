<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.lowDegreeOutsideInfluentialMass_le_sum_coordinateMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate bound for low-degree mass

**Claim.** The low-degree Fourier mass on sets not contained in the influential coordinates is at most the sum, over coordinates of influence less than $\tau$, of the low-degree Fourier masses on sets containing those coordinates.

**Proof.** Let the summation run over sets $S$ with $|S|\le k$ that are not contained in the influential coordinates. Each such $S$ contains some coordinate $i$ outside the influential set. Thus its nonnegative Fourier weight can be counted among the contributions from coordinates outside that set which lie in $S$; in the proof this is first witnessed by the singleton coordinate $\{i\}$ and then bounded by summing over all coordinates. After restricting the set sum to the low-degree sets, the indicator condition is exactly that $i$ is outside the influential set, belongs to $S$, and $|S|\le k$. Interchanging the finite sums therefore gives the sum, over coordinates outside the influential set, of the low-degree masses on sets containing each coordinate. The characterization of being outside the influential set as having influence less than $\tau$ (`not_mem_influentialCoordinates`) gives the stated form.

**Key facts.** `FABL.not_mem_influentialCoordinates`.
