<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_inverse_square_exp_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential inverse-square bound

**Claim.** For every real $t>0$, $e^{-2t}\le (t^{-1})^2$.

**Proof.** Since $t>0$, the logarithmic inequality $\log t\le t-1$ gives $-2t\le -2\log t$ (indeed, $-2t\le -2\log t-2$, which is stronger). Monotonicity of the exponential therefore yields $e^{-2t}\le e^{-2\log t}$. Write the latter as $(e^{-\log t})^2$ using the exponential addition law; since $t>0$, $e^{\log t}=t$, so $e^{-\log t}=t^{-1}$. Thus $e^{-2t}\le (t^{-1})^2$.
