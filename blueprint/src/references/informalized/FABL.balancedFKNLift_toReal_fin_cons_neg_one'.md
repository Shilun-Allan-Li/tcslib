<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.balancedFKNLift_toReal_fin_cons_neg_one' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Lift at Negative Leading Sign

**Claim.** After interpreting outputs as real numbers, the balanced lift at leading coordinate $-1$ and tail $x$ equals $-f(-x)$.

**Proof.** First apply the negative-leading-sign identity for the sign-valued lift (`balancedFKNLift_fin_cons_neg_one`). The real-valued claim then follows by checking the two possible values, $1$ and $-1$, of $f(-x)$: their real interpretations satisfy the same negation identity.

**Key facts.** `FABL.balancedFKNLift_fin_cons_neg_one`.
