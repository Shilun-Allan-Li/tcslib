<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.linear_form_tail_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear form tail expectation

**Claim.** For a normalized linear form on the Boolean cube and $s\ge1$, its expected magnitude restricted to the event $|L|\ge s$ is at most $(2s+2)e^{-s^2/2}$.

**Proof.** Write $L(x)=\sum_i a_i\operatorname{boolToSign}(x_i)$ and set $K=(s+1)e^{-s^2}$. For any $y\ge s$, put $v=y-s\ge0$. Since $e^{sv}\ge1+sv\ge1+v$ when $s\ge1$, we have $y=s+v\le(s+1)(1+v)\le(s+1)e^{sv}=K e^{sy}$. Applying this to $y=|L(x)|$ and considering whether $L(x)$ is nonnegative or nonpositive gives the pointwise bound
\[\mathbf 1_{\{|L(x)|\ge s\}}|L(x)|\le K\bigl(e^{sL(x)}+e^{-sL(x)}\bigr).\]
Take expectations and use monotonicity and linearity of expectation. The Rademacher moment-generating-function bound, under $\sum_i a_i^2=1$, gives $\mathbb E e^{tL}\le e^{t^2/2}$ for each real $t$ (`rademacher_mgf_le`); applying it at $s$ and $-s$ bounds the expectation by $2K e^{s^2/2}=2(s+1)e^{-s^2/2}=(2s+2)e^{-s^2/2}$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.rademacher_mgf_le`.
