<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.isFourierRegular_leadingCoordinateTimes_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate-Times-Majority Regularity

**Claim.** For every natural number $m$, the function obtained by multiplying the first coordinate by majority on the remaining $2m+1$ coordinates has all nonempty-set Fourier coefficients bounded in absolute value by $1/\sqrt{2m+1}$.

**Proof.** Majority on an odd number of coordinates is Fourier regular at the stated threshold, and it is balanced. The result that multiplying a balanced Boolean function by a new leading coordinate preserves its Fourier regularity therefore applies. The threshold is nonnegative, as required by that result, so the claimed regularity follows.

**Key facts.** `FABL.isFourierRegular_majority_odd`, `FABL.isBalanced_majority_odd`, `FABL.IsFourierRegular.leadingCoordinateTimes_of_isBalanced`.
