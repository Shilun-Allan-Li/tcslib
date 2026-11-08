<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.fourierCoeff_balancedFKNLift_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted Tail Singleton Coefficient

**Claim.** For the balanced lift, the Fourier coefficient at singleton coordinate $i+1$ equals the original function's coefficient at singleton coordinate $i$.

**Proof.** The frequency consisting of coordinate $i+1$ is the tail embedding of the singleton frequency $\{i\}$. Its coefficient is the average of the coefficients of the two first-coordinate slices (FABL.fourierCoeff_tailFrequency). For the slice with first coordinate $1$, the lifted function reduces to $f$ (FABL.balancedFKNLift_toReal_fin_cons_one). For the slice with first coordinate $-1$, it is $x\mapsto-f(-x)$ (FABL.balancedFKNLift_toReal_fin_cons_neg_one). The coefficient of this latter function at a set $S$ is $-(-1)^{|S|}$ times the coefficient of $f$ at $S$ (FABL.fourierCoeff_negatedInput_toReal). Since $|\{i\}|=1$, this factor is $1$, so both slice coefficients equal the original coefficient. Their average is therefore that same coefficient.

**Key facts.** `FABL.fourierCoeff_tailFrequency`, `FABL.balancedFKNLift_toReal_fin_cons_one`, `FABL.balancedFKNLift_toReal_fin_cons_neg_one`, `FABL.fourierCoeff_negatedInput_toReal`.
