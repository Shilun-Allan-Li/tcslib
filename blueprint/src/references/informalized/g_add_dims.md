<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: g_add_dims -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# An additive dimension identity for isotropic subspaces

**Claim.** Let $S$ be an isotropic submodule of the symplectic space $V=\mathbb{F}_p^n\times\mathbb{F}_p^n$, let $M\subseteq\{0,\dots,n-1\}$ be a set of coordinates with complement $M^c$, and write $S_M=S\cap V_M$ and $S_{M^c}=S\cap V_{M^c}$ for the parts of $S$ supported on $M$ and on $M^c$. Then
\[
g(S,M)+\dim_{\mathbb{F}_p}(S_M)+\dim_{\mathbb{F}_p}(S)\;=\;2\lvert M\rvert+\dim_{\mathbb{F}_p}(S_{M^c}),
\]
where $g(S,M)=\dim(S^\perp\cap V_M)-\dim(S_M)$.

**Proof.** Throughout, $V_M$ denotes the submodule of vectors both of whose halves vanish outside $M$; it has dimension $2\lvert M\rvert$ (`dim_V_sub`). We write $S^\perp$ for the orthogonal complement of $S$ with respect to the symplectic form $\omega(u,v)=\sum_i\bigl(u_1(i)v_2(i)-u_2(i)v_1(i)\bigr)$, and $\rho_M\colon V\to V$ for the coordinate restriction that zeroes out every coordinate not in $M$ (so its image lies in $V_M$). All dimensions are over $\mathbb{F}_p$, and all subtractions below are of natural numbers — a point the proof must watch, since truncated subtraction only agrees with genuine subtraction when the subtrahend is no larger than the minuend.

The proof rests on a closed formula for $g$ and then does the arithmetic needed to turn a truncated difference into a genuine equation.

1. **The defining formula for $g$.** The companion computation (`g_formula`) evaluates $g(S,M)$ as the natural-number difference
\[
g(S,M)=\bigl(2\lvert M\rvert+\dim S_{M^c}\bigr)-\bigl(\dim S+\dim S_M\bigr).
\]
Write $A=2\lvert M\rvert+\dim S_{M^c}$ and $B=\dim S+\dim S_M$, so this reads $g(S,M)=A-B$. The goal of the lemma is exactly $g(S,M)+B=A$. In $\mathbb{N}$ the equation $g(S,M)+B=A$ holds, given $g(S,M)=A-B$, if and only if the subtraction is not truncated — that is, if and only if $B\le A$. (Formally the Lean proof reaches this reduction by contraposition together with the characterisation $a=c-b\iff a+b=c$ valid when $b\le c$; mathematically the one thing left to prove is the inequality $B\le A$.)

2. **Rank–nullity for the restriction $\rho_M$.** Restricting $\rho_M$ to $S$, its kernel is precisely the set of vectors of $S$ supported off $M$, namely $S\cap V_{M^c}=S_{M^c}$. Hence (`dim_map_r_E`)
\[
\dim\rho_M(S)=\dim S-\dim S_{M^c}.
\]
That this is a genuine, non-truncated subtraction is guaranteed by $\dim S_{M^c}\le\dim S$, which follows from the inequality $\dim S_M+\dim S_{M^c}\le\dim S$ (`dim_S_M_add_dim_S_M_c_le_dim_S`) by dropping the first summand.

3. **The orthogonal part on $M$.** A dimension count for the orthogonal complement intersected with $V_M$ (`dim_orth_inter`) gives
\[
\dim\bigl(S^\perp\cap V_M\bigr)=2\lvert M\rvert-\dim\rho_M(S).
\]
Again this is a genuine subtraction because $\rho_M(S)\subseteq V_M$ forces $\dim\rho_M(S)\le\dim V_M=2\lvert M\rvert$ (using `dim_V_sub`). Substituting the value of $\dim\rho_M(S)$ from Step 2,
\[
\dim\bigl(S^\perp\cap V_M\bigr)=2\lvert M\rvert-\dim S+\dim S_{M^c}.
\]

4. **Using isotropy.** Because $S$ is isotropic, $S\le S^\perp$, and intersecting both sides with $V_M$ gives $S_M=S\cap V_M\le S^\perp\cap V_M$. Monotonicity of dimension under inclusion then yields
\[
\dim S_M\le\dim\bigl(S^\perp\cap V_M\bigr)=2\lvert M\rvert-\dim S+\dim S_{M^c}.
\]
Rearranging, $\dim S+\dim S_M\le 2\lvert M\rvert+\dim S_{M^c}$, which is exactly the inequality $B\le A$ sought in Step 1.

5. **Conclusion.** Since $B\le A$, the difference $A-B$ in the formula of Step 1 is a true subtraction, so $g(S,M)+B=A$, i.e.
\[
g(S,M)+\dim S_M+\dim S=2\lvert M\rvert+\dim S_{M^c},
\]
as claimed.

**Key facts.** `g_formula`, `dim_S_M_add_dim_S_M_c_le_dim_S`, `dim_map_r_E`, `dim_orth_inter`, `dim_V_sub`.
