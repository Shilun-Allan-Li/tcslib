<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.balancedFKNLift_toReal_fin_cons_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Lift at Positive Leading Sign

**Claim.** After interpreting outputs as real numbers, the balanced lift at leading coordinate $1$ and tail $x$ equals $f(x)$.

**Proof.** The sign-valued lift at this input equals $f(x)$ by the positive-leading-sign identity (`balancedFKNLift_fin_cons_one`). Applying the real interpretation to both sides gives the asserted equality.

**Key facts.** `FABL.balancedFKNLift_fin_cons_one`.
