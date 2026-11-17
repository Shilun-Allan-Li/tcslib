<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.pBiasedFourierFailure_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Containment of Fourier failure sets

**Claim.** If the empty-set coefficient differs from $p$ by more than the threshold, or some nonempty-set coefficient exceeds the threshold in absolute value, then some coordinate set has deviation at least the threshold from its prescribed value ($p$ for the empty set and zero otherwise).

**Proof.** Take a function in the failure set. If its empty-set coefficient differs from $p$ by more than the threshold, choose the empty set; the strict inequality implies the required weak inequality. Otherwise, choose a nonempty set whose coefficient has absolute value greater than the threshold. Its prescribed value is zero, so again the strict inequality implies the required weak inequality. In either case the function lies in the corresponding member of the union, and hence in the union itself.
