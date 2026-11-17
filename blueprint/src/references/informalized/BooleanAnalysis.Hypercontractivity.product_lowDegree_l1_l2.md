<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_l1_l2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree L1–L2 Comparison

**Claim.** For a low-degree function on a finite product space with atom weights bounded below by λ≤1/2, its second norm is at most the kth power of the product norm comparison constant times its first norm.

**Proof.** Split into λ<1/2 and λ=1/2. In the strict case, the strict-parameter estimate gives the conclusion directly. At the endpoint λ=1/2, approach it from below through parameters a in (0,1/2). The atom lower bound for λ=1/2 implies the corresponding bound for every such a, so the strict estimate applies at each a. The comparison constants converge to e as a tends to 1/2 from below; taking the limit in the inequalities, with k fixed and the first norm constant, gives the endpoint estimate.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_lowDegree_l1_l2_lt_half`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.constant_tendsto_half`.
