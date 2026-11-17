<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.fourierCoeff_balancedFKNLift_succ' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted Tail Singleton Coefficient

**Claim.** For the balanced lift, the Fourier coefficient at singleton coordinate $i+1$ equals the original function's coefficient at singleton coordinate $i$.

**Proof.** Identify the singleton frequency $\{i+1\}$ with the tail embedding of $\{i\}$. The tail-frequency coefficient formula expresses it as the average of the coefficients of the two slices at first coordinate $1$ and $-1$ (FABL.fourierCoeff_tailFrequency). The first slice is $f$ (FABL.balancedFKNLift_toReal_fin_cons_one'), while the second is $x\mapsto-f(-x)$ (FABL.balancedFKNLift_toReal_fin_cons_neg_one'). Negating the input and the function changes the coefficient at a set $S$ by the factor $-(-1)^{|S|}$ (FABL.fourierCoeff_negatedInput_toReal'). For a singleton this factor is $1$, so both slices have the original coefficient at $\{i\}$. Their average gives the claimed equality.

**Key facts.** `FABL.fourierCoeff_tailFrequency`, `FABL.balancedFKNLift_toReal_fin_cons_one'`, `FABL.balancedFKNLift_toReal_fin_cons_neg_one'`, `FABL.fourierCoeff_negatedInput_toReal'`.
