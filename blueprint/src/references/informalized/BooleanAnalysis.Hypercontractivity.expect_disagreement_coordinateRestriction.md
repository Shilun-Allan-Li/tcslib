<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Rounding.lean :: BooleanAnalysis.Hypercontractivity.expect_disagreement_coordinateRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement Under Coordinate Restriction

**Claim.** For a Boolean-valued function $f$ and a coordinate set $J$, the average over $z$ of the disagreement probability between $f$ and $x\mapsto f(x_J,z_{[n]\setminus J})$ equals half the sum of squared Fourier coefficients over subsets not contained in $J$.

**Proof.** 1. Since both values of $f$ are in $\{-1,1\}$, their disagreement indicator is $\frac12(1-f(x)f(x_J,z_{[n]\setminus J}))$. Indeed, the product is $1$ when they agree and $-1$ when they differ.

2. For each fixed $x$, the expected restricted value has Fourier expansion over the sets contained in $J$ (\texttt{expect\_coordinateRestriction\_eq\_sum\_fourier}). Multiplying by $f(x)$ and averaging over $x$, each retained term contributes its Fourier coefficient squared: the expected product $f(x)\chi_S(x)$ is the coefficient of $S$. Hence the correlation between $f$ and the averaged restriction is $\sum_{S\subseteq J}\widehat f(S)^2$.

3. Average the disagreement-indicator identity over both $x$ and $z$. The two finite uniform averages can be interchanged (\texttt{expect\_eq\_fintypeExpect} and finite-sum interchange). The resulting disagreement is half of one minus the correlation just computed. Parseval for a Boolean-valued function says that the sum of all squared Fourier coefficients is $1$ (\texttt{parseval\_pm\_one}); subtracting the contribution from sets contained in $J$ leaves exactly the squared weight on sets not contained in $J$. This gives the claimed formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_coordinateRestriction_eq_sum_fourier`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.parseval_pm_one`.
