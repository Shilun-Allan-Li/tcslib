<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.anisotropicNoise_norm_le_of_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anisotropic noise contraction

**Claim.** If every coordinate noise operator is contractive in the product norm, then the anisotropic noise operator is contractive in that norm.

**Proof.** Induct on the finite set $J$ of coordinates on which partial noise is applied. For $J=\varnothing$, the partial operator is the identity: the component reconstruction formula says that summing all components recovers $f$, and the empty product contributes coefficient $1$. Thus its norm equals the norm of $f$. For the induction step, write $J'=\{i\}\cup J$ with $i\notin J$. The insertion identity for partial noise expresses the operator for $J'$ as coordinate noise in coordinate $i$ applied to the operator for $J$ (\texttt{partialNoise\_insert}). By the assumed coordinate contraction, its norm is at most the norm after applying partial noise on $J$, which is at most $\|f\|_{q,P}$ by induction. Finally take $J$ to be the full coordinate set: partial noise then agrees with anisotropic noise, giving the desired inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_reconstruction`, `BooleanAnalysis.Hypercontractivity.partialNoise_insert`.
