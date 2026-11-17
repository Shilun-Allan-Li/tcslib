<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.two_div_nandGrowthRate_add_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND Growth Rate Identity

**Claim.** For $r=(1+\sqrt{33})/4$, one has $2/r+1/2=r$.

**Proof.** The growth rate is positive (`FABL.nandGrowthRate_pos`), so it is nonzero and we may clear the denominator. The resulting identity is equivalent to $r^2=r/2+2$, which is the square relation supplied by `FABL.nandGrowthRate_sq`.

**Key facts.** `FABL.nandGrowthRate_pos`, `FABL.nandGrowthRate_sq`.
