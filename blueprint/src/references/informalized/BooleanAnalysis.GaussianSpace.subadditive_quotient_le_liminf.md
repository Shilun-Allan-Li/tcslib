<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.subadditive_quotient_le_liminf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subadditive Secants Bound the Right Liminf

**Claim.** If $f(0)=0$, $f$ is continuous at zero, and $f$ is subadditive, then for every $\delta>0$, $\operatorname{ENNReal.ofReal}(f(\delta)/\delta)$ is at most the right-hand liminf of $\operatorname{ENNReal.ofReal}(f(t)/t)$ as $t\to0^+$.

**Proof.** Use the characterization of an extended-real liminf by comparison with every strict lower bound $b$ of the proposed left-hand side. Fix such a $b$; the strict comparison translates into $b.toReal\,\delta<f(\delta)$. By continuity at zero and $f(0)=0$, choose $\varepsilon>0$ so that whenever $0\le r<\varepsilon$, one has $f(r)<f(\delta)-b.toReal\,\delta$. Consider any $t$ with $0<t<\varepsilon$, and let $k=\lfloor\delta/t\rfloor$. The floor inequalities give $kt\le\delta$ and $0\le r:=\delta-kt<t$. Thus the remainder $r$ lies in the continuity neighborhood, and $f(r)<f(\delta)-b.toReal\,\delta$. Repeated subadditivity gives $f(kt)\le kf(t)$, including the case $k=0$. Applying subadditivity once more to $\delta=kt+r$ yields $f(\delta)\le f(kt)+f(r)$. Combining these inequalities shows $k f(t)>b.toReal\,\delta$. If $f(t)/t$ were at most $b.toReal$, then $k f(t)\le b.toReal\,kt\le b.toReal\,\delta$, since $b$ is nonnegative, a contradiction. Hence the truncated quotient at every such $t$ exceeds $b$, which proves the liminf comparison for every strict lower bound $b$.
