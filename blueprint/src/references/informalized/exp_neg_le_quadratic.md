<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: exp_neg_le_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bound for the negative exponential

**Claim.** For every real $t\ge0$, $e^{-t}\le1-t+t^2/2$.

**Proof.** The exponential lower bound gives $e^t\ge1+t+t^2/2$ for $t\ge0$, and $1-t+t^2/2>0$. Multiplying the lower bound by this positive quadratic shows that $e^t(1-t+t^2/2)$ is at least $(1+t+t^2/2)(1-t+t^2/2)=1+t^4/4\ge1$. Dividing by the positive quantity $e^t$ gives $e^{-t}\le1-t+t^2/2$.
