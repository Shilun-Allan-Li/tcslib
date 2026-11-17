<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.balancedFKNLift_toReal_fin_cons_one' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Lift at Positive Leading Sign

**Claim.** After interpreting outputs as real numbers, the balanced lift at leading coordinate $1$ and tail $x$ equals $f(x)$.

**Proof.** By the positive-leading-sign identity for the sign-valued lift (`balancedFKNLift_fin_cons_one`), its value at this input is exactly $f(x)$. Interpreting both outputs as real numbers preserves that equality.

**Key facts.** `FABL.balancedFKNLift_fin_cons_one`.
