<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: exp_convexity_bound' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity bound for the exponential

**Claim.** For every real $\eta$ and every $x\in[0,1]$, $e^{-\eta x}\le 1-x+xe^{-\eta}$.

**Proof.** The exponential is convex on $\mathbb R$. Apply its two-point convexity inequality to the points $0$ and $-\eta$ with weights $1-x$ and $x$, which are nonnegative and sum to one. The corresponding convex combination of the points is $(1-x)0+x(-\eta)=-\eta x$, while the same combination of their exponential values is $(1-x)e^0+xe^{-\eta}=1-x+xe^{-\eta}$. This gives the claimed inequality.
