<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.balancedFKNLift_fin_cons_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Lift at Negative Leading Sign

**Claim.** For the balanced lift of $f$, evaluation at the vector with leading coordinate $-1$ and tail $x$ is $-f(-x)$.

**Proof.** Evaluate the lift at $z=(-1,x)$. Its leading factor is $-1$, and each tail coordinate is multiplied by that same leading sign, so the input to $f$ is $-x$. Therefore the value is $(-1)f(-x)=-f(-x)$. Equality of these sign-valued outputs follows by checking their underlying integer values.
