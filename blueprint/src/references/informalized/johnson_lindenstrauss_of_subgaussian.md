<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean :: johnson_lindenstrauss_of_subgaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sub-Gaussian Johnson–Lindenstrauss embedding

**Claim.** Under the stated projection measurability, independence, sub-Gaussian moment-generating-function, and variance assumptions, the pairwise failure bound and union-bound hypothesis imply a linear map preserving all squared distances in the finite set within relative error ε.

**Proof.** Fix $u,v\in V$ and put $x=u-v$. If $x=0$, the bad event is empty up to the zero-vector concentration bound, so its probability satisfies the required estimate. If $x\ne0$, apply the sub-Gaussian single-vector concentration theorem to the independent row projections of $x$; the given moment-generating-function and second-moment bounds provide its hypotheses and yield the same bound $2\exp(-k\varepsilon^2/8)$. Hence this estimate holds for every pair. The measurable bad events have total probability at most $|V|^2$ times that bound. Since the assumed total is less than one, some outcome avoids every bad event; its matrix defines the required linear embedding.

**Key facts.** `concentration_zero`, `jl_concentration_single_subgaussian`, `exists_isJLEmbedding_of_pair_bound`.
