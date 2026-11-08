<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_scalar_dichotomy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar KKL dichotomy

**Claim.** Under the stated bounds on $L,D,x,t$, either $\frac{x}{100Le^x}\le\frac{t}{e^x}$ or $\frac{x}{100Le^x}\le t^{-2}e^{-Dt}$.

**Proof.** First, $100L>0$ follows from $2\le100L$. Split according to whether $x\le100Lt$. In that case, dividing by the positive quantities and using $e^x\ge0$ gives the first alternative. Otherwise $100Lt<x$. Together with $2(D+2)\le100L$ and $t>0$, this implies $(D+2)t<x/2$. For this second case, bound the left side as follows: $x/(100Le^x)=(x/(100L))/e^x$. Since $x\ge0$ and $100L\ge2$, we have $x/(100L)\le x/2$; and $x/2\le e^{x/2}$ by the elementary exponential bound. Thus the ratio is at most $e^{-x/2}$, which is at most $e^{-(D+2)t}$. Factoring this as $e^{-2t}e^{-Dt}$ and applying the inverse-square exponential bound ($\texttt{kkl\_inverse\_square\_exp\_lower}$) gives the second alternative.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_inverse_square_exp_lower`.
