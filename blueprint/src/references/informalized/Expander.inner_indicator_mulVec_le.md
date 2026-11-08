<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Mixing.lean :: Expander.inner_indicator_mulVec_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expander Mixing Bound for Subsets

**Claim.** For a symmetric stochastic matrix whose nontrivial operator norm is at most $\lambda$, the deviation of $\langle 1_S,A1_T\rangle$ from $|S||T|/n$ is at most $\lambda\sqrt{|S||T|}$.

**Proof.** Let $u$ be the uniform vector. First, summing its constant coordinates against an indicator gives $\langle 1_U,u\rangle=|U|/n$ for each subset $U$, and $\langle u,u\rangle=1/n$ (`inner_uniform_self`). Remove the uniform components by setting $s=1_S-(|S|/n)\mathbf{1}$ and $t=1_T-(|T|/n)\mathbf{1}$, where $\mathbf{1}$ here denotes the constant vector $u$ scaled by $n$. The inner product calculations using the indicator averages show $s,t\perp u$. Since the matrix fixes $u$ (`mulVec_uniform`), and symmetry allows it to be moved from one side of the inner product to the other (`inner_toCLM_right`), the mixed terms vanish. The remaining uniform term is $|S||T|/n$, so the deviation in the claim is exactly $\langle s,At\rangle$. Orthogonal projection cannot increase norm: applying the Pythagorean identity to each indicator and its uniform component gives $\|s\|\le\|1_S\|=\sqrt{|S|}$ and $\|t\|\le\|1_T\|=\sqrt{|T|}$. By Cauchy–Schwarz and the bound defining the nontrivial operator norm (`norm_mulVec_le_lambda`), $|\langle s,At\rangle|\le\|s\|\lambda(A)\|t\|$. Finally, $\lambda(A)\le\lambda$ and $\lambda\ge0$: the latter follows because the supremum defining $\lambda(A)$ is a supremum of norms. Combining these inequalities and using $\sqrt{|S|}\sqrt{|T|}=\sqrt{|S||T|}$ proves the result.

**Key facts.** `Expander.inner_uniform_self`, `Expander.mulVec_uniform`, `Expander.inner_toCLM_right`, `Expander.norm_mulVec_le_lambda`.
