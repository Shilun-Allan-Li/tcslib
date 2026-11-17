<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Coalitional Influence

**Claim.** The coalitional influence of a Boolean function toward either sign is nonnegative.

**Proof.** For every input $x$ with $f(x)=b$, the coalition can attain $b$ by leaving all coordinates unchanged: choose the witness input $y=x$. Thus the event that $f(x)=b$ is contained in the event that the coalition can attain $b$. Uniform probability is monotone under inclusion, so the coalition success probability is at least the original probability of output $b$. Their difference, the coalitional influence toward $b$, is therefore nonnegative.

**Key facts.** `FABL.coalitionCanAttain_current`, `FABL.uniformProbability_mono`.
