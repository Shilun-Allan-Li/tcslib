<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Elementary.lean :: KKL.friedgut_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Friedgut’s junta approximation

**Claim.** For a Boolean function $f$ and $\epsilon>0$, there are a coordinate set $J$ and a function $g$ depending only on $J$ such that $|J|\le 4n I[f]/\epsilon$ and the squared $L^2$ distance from $f$ to $g$ is at most $\epsilon$.

**Proof.** Write $I=I[f]$. The proof first establishes three ingredients. The degree truncation at level $k>0$ approximates $f$ with squared $L^2$ error at most $I/k$ (KKL.lowDegree_approx). Also, for any $k$ and threshold $\tau>0$, the truncation can be approximated with squared error at most $n\tau$ by a function depending only on the coordinates whose influences are at least $\tau$ (KKL.lowDegreePart_depends_on_influential); the number of these coordinates is at most $I/\tau$ (KKL.influential_coords_card). Finally, the squared-distance triangle estimate gives $\|f-g\|_2^2\le 2\|f-h\|_2^2+2\|h-g\|_2^2$ for any intermediate function $h$.

If $I\le0$, the Fourier formula for total influence expresses $I$ as a sum of nonnegative terms $|S|\widehat f(S)^2$, so in fact $I=0$. When $n=0$, the cube has a single point, and taking $J=\varnothing$ and $g=f$ proves the result. When $n>0$, take $k=1$ and $\tau=\epsilon/(2n)$. The degree truncation has zero error because its error is at most $I/1=0$, and its junta approximation has error at most $n\tau=\epsilon/2$. The triangle estimate therefore gives total squared error at most $\epsilon$. The junta size bound is $I/\tau=0$, which satisfies the stated bound.

If $I>0$, take $k=\lceil 4I/\epsilon\rceil$ and $\tau=\epsilon/(4n)$. These are positive, since this case forces $n>0$. The ceiling choice ensures $I/k\le\epsilon/4$, while $n\tau=\epsilon/4$. Apply the two approximation ingredients in sequence, with the degree truncation as the intermediate function. The triangle estimate gives squared error at most $2(\epsilon/4)+2(\epsilon/4)=\epsilon$. The junta has size at most $I/\tau=4nI/\epsilon$, as required.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `KKL.lowDegree_approx`, `KKL.lowDegreePart_depends_on_influential`, `KKL.influential_coords_card`.
