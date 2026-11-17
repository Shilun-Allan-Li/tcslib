<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Moments.lean :: BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral of a Multilinear Evaluation

**Claim.** For mutually independent coordinates with mean zero, second moment one, and finite fourth moments, the integral of the multilinear evaluation equals its coefficient at the empty set.

**Proof.** Apply the product-integral identity for two multilinear evaluations with the second coefficient family equal to $1$ at the empty set and $0$ elsewhere. Its evaluation is the constant function $1$: the empty-set term contributes $1$, while every nonempty-set term has coefficient zero. The product-integral identity therefore says that the integral of the original evaluation times $1$ is the sum over all sets $S$ of $F(S)$ times this second coefficient. Only the empty-set term remains, giving $F(\varnothing)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval_mul`.
