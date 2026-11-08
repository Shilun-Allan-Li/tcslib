<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.fkn_closeness_improvement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improved FKN Closeness Bound

**Claim.** If the FKN theorem holds with closeness bound $C\delta$ for some $C\ge1$, then it also holds with closeness bound $\delta/4+16C^2\delta^2\max(\log(1/(C\delta)),1)$.

**Proof.** Fix a function and parameters satisfying the hypotheses, and use the assumed FKN bound to choose a coordinate $i$ and sign $s\in\{-1,1\}$ such that the disagreement probability $\eta$ between $f$ and $s$ times the dictator at $i$ is at most $\varepsilon=C\delta$. Pointwise nonnegativity of the disagreement indicator gives $\eta\ge0$, and comparison with the constant-one function gives $\eta\le1$. If $\varepsilon=0$, then $C\ge1$ implies $\delta=0$, and the original closeness bound already gives the result. If $\varepsilon\ge1/4$, then $16\varepsilon^2\ge1$ and the logarithmic maximum is at least one, so the proposed bound is at least one and hence at least $\eta$.

It remains to consider $0<\varepsilon<1/4$. For each bit $b$, let $r_b$ be the restriction of $f$ obtained by fixing coordinate $i$ to $b$, and let $d_b$ indicate disagreement of this restriction with the constant $s\,\sigma(b)$. Averaging over the two values of coordinate $i$ recovers the original expectation: this follows by pairing each cube point with its coordinate flip, whose flip map is an involution (`flipBit_flipBit`). Consequently $\eta=(\mathbb E d_0+\mathbb E d_1)/2$. Both restricted disagreement expectations are nonnegative, so each is at most $2\varepsilon$.

Because $f$ and the comparison function take values in $\{-1,1\}$, pointwise their signed product equals $1-2d_b$. Taking expectations shows that the signed mean of each restriction is $1-2\mathbb E d_b$; its absolute mean is therefore at least $1-4\varepsilon$. Apply the biased degree-one weight bound (`biased_degreeOne_weight`) to each restriction with bias parameter $4\varepsilon$. Since $4\varepsilon<1$, its hypothesis holds, and the resulting estimate is $W_1[r_b]\le64\varepsilon^2\log(1/(2\varepsilon))$.

For every coordinate $j\ne i$, the Fourier coefficient of $f$ at $\{j\}$ is the average of the corresponding coefficients of the two restrictions. The square of an average is at most the average of the squares. Summing over $j\ne i$, and bounding by the full degree-one weights of the restrictions, therefore gives total squared Fourier mass outside coordinate $i$ at most $64\varepsilon^2\log(1/(2\varepsilon))$.

The selected coefficient also records the disagreement: $s\widehat f(\{i\})=1-2\eta$, so its square is $(1-2\eta)^2$. Decomposing the degree-one weight into this coefficient and all the others, the hypothesis $W_1[f]\ge1-\delta$ implies
\[
1-\delta\le (1-2\eta)^2+64\varepsilon^2\log(1/(2\varepsilon)).
\]
Rearranging gives $\eta\le\delta/4+\eta^2+16\varepsilon^2\log(1/(2\varepsilon))$. Since $0\le\eta\le\varepsilon$, we have $\eta^2\le\varepsilon^2$. Also $\log 2\ge1/2$; hence this square term is at most $16\varepsilon^2\log2$. Using $\log(1/(2\varepsilon))=\log(1/\varepsilon)-\log2$ absorbs the square term and yields $\eta\le\delta/4+16\varepsilon^2\log(1/\varepsilon)$. Finally, $\varepsilon=C\delta$, and $\log(1/(C\delta))\le\max(\log(1/(C\delta)),1)$. Substitution gives the claimed closeness bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_nonneg`, `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.ThresholdFunctions.expect_sub`, `BooleanAnalysis.ThresholdFunctions.biased_degreeOne_weight`, `BooleanAnalysis.chiS_singleton`, `BooleanAnalysis.ThresholdFunctions.weightLevel_one_eq_sum_singleton`, `BooleanAnalysis.flipBit_flipBit`.
