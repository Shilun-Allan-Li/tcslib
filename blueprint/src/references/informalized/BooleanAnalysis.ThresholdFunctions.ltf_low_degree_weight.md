<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.ltf_low_degree_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight of a linear threshold function

**Claim.** Every linear threshold function has Fourier weight through degree one at least $1/2$.

**Proof.** Apply the low-degree Fourier weight bound with $k=1$ and $c=1/2$. It remains to verify its norm hypothesis for every affine coefficient family $p$ of degree at most one. The affine Khintchine inequality states that $\sum_S p(S)^2\le2(\mathbb E|p|)^2$ (`affine_khintchine_sq`), which is exactly the required inequality after multiplying by $1/2$. The low-degree Fourier weight bound (`le_fourierWeightUpTo_of_l1_l2`) then gives $1/2\le W_{\le1}[f]$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.affine_khintchine_sq`, `BooleanAnalysis.ThresholdFunctions.le_fourierWeightUpTo_of_l1_l2`.
