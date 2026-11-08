<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.selfAdjoint_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction from self-adjointness

**Claim.** A self-adjoint operator that contracts the weighted norm at exponent $q/(q-1)$ also contracts the weighted norm at exponent $q$, for $q>1$.

**Proof.** Fix $f$ and let $N$ be its weighted $q$-norm, which is nonnegative. To apply the norm bound from pairings (`BooleanAnalysis.Hypercontractivity.FiniteNorms.norm_le_of_pairing`) to $Tf$, consider any $g$. Self-adjointness moves the operator from the first entry of the weighted pairing to the second, giving the pairing of $f$ with $Tg$. Weighted Hölder's inequality (`BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_holder`) bounds this by $N$ times the weighted norm of $Tg$ at exponent $q/(q-1)$. The assumed contraction at that exponent bounds the latter norm by the corresponding norm of $g$. Thus every pairing against $Tf$ satisfies the hypothesis of the norm bound, which yields the desired $q$-norm contraction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.norm_le_of_pairing`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_holder`.
