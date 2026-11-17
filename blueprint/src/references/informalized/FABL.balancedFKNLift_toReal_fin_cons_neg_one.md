<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.balancedFKNLift_toReal_fin_cons_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Lift at Negative Leading Sign

**Claim.** After interpreting outputs as real numbers, the balanced lift at leading coordinate $-1$ and tail $x$ equals $-f(-x)$.

**Proof.** The sign-valued evaluation of the lift at this input is $-f(-x)$, by the negative-leading-sign identity (`balancedFKNLift_fin_cons_neg_one`). Interpreting both sides as real numbers reduces the claim to the two possible sign values of $f(-x)$: if that value is $1$, both sides are $-1$; if it is $-1$, both sides are $1$.

**Key facts.** `FABL.balancedFKNLift_fin_cons_neg_one`.
