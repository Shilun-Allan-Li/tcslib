<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.fourierCoeff_balancedFKNLift_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# New-Coordinate Coefficient of the Lift

**Claim.** The Fourier coefficient of the balanced lift at the singleton consisting of the new coordinate equals the original function's constant Fourier coefficient.

**Proof.** The new-coordinate singleton is the union of coordinate $0$ with the tail embedding of the empty frequency. The coefficient formula for such a frequency is half the first slice's empty coefficient minus half the second slice's empty coefficient (FABL.fourierCoeff_insert_zero_tailFrequency). The first slice is $f$ (FABL.balancedFKNLift_toReal_fin_cons_one), and the second is $x\mapsto-f(-x)$ (FABL.balancedFKNLift_toReal_fin_cons_neg_one). At the empty frequency the negated-input identity says the latter coefficient is the negative of the original constant coefficient, since the empty set has cardinality zero (FABL.fourierCoeff_negatedInput_toReal). Substituting gives one half of the original coefficient minus its negative, hence exactly the original constant coefficient.

**Key facts.** `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.balancedFKNLift_toReal_fin_cons_one`, `FABL.balancedFKNLift_toReal_fin_cons_neg_one`, `FABL.fourierCoeff_negatedInput_toReal`.
