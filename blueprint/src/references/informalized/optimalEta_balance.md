<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: optimalEta_balance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balance of two positive terms

**Claim.** For positive $a,T,c$, the sum $a/\sqrt{ca/T}+\sqrt{ca/T}\,T/c$ equals $\sqrt{4aT/c}$.

**Proof.** Put $s=\sqrt{ca/T}$, so $s>0$ and $s^2T=ca$. This identity implies $a/s=sT/c$, since multiplying the equality by the positive denominators reduces it to $s^2T=ca$. Thus the left side is $2sT/c$, a positive quantity. Its square is $4s^2T^2/c^2=4aT/c$, again using $s^2T=ca$. Since both sides are nonnegative and have the same square, $2sT/c=\sqrt{4aT/c}$, proving the formula.
