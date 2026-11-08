<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.exercise5_38_sqrt_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-root lower bound

**Claim.** Under the stated bounds on $C$ and $\delta$, if $A\ge0$ and the given expression is at most $A$, then $1-\delta/2-2\eta(C,\delta)\le\sqrt A$.

**Proof.** Apply the nonnegative lower-bound result (`FABL.exercise5_38_nonnegative_lower_bound`) with $z=\sqrt A$. The square root is nonnegative, and its square is $A$ because $A\ge0$. Thus the assumed bound on $A$ is precisely the required squared estimate, and the conclusion follows.

**Key facts.** `FABL.exercise5_38_nonnegative_lower_bound`.
