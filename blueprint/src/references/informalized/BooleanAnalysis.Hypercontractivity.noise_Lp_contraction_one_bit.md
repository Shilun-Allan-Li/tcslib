<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.noise_Lp_contraction_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# $L^q$-contractivity of the one-bit noise operator

**Claim.** Fix an exponent $q \ge 1$ and a noise parameter $\rho$ with $0 \le \rho \le 1$. For every function $g\colon\{0,1\}^1\to\mathbb{R}$ on a single bit, the spectral noise operator $T_\rho$ does not increase the $L^q$-norm: $\bigl(\mathbb{E}\,|T_\rho g|^q\bigr)^{1/q}\le\bigl(\mathbb{E}\,|g|^q\bigr)^{1/q}$, where both expectations are with respect to the uniform measure on the two points of $\{0,1\}^1$.

**Proof.** Because the cube $\{0,1\}^1$ has only two points, everything reduces to a scalar inequality in the two Fourier coefficients of $g$. Write
\[
a=\widehat{g}(\varnothing),\qquad b=\widehat{g}(\{0\}),
\]
the only subsets of $\{0\}$ being $\varnothing$ and $\{0\}$.

1. **Unwinding the definitions at the two points.** The uniform expectation of any $F\colon\{0,1\}^1\to\mathbb{R}$ is the plain average $\tfrac12\bigl(F(\mathbf 0)+F(\mathbf 1)\bigr)$ over the two points $\mathbf 0,\mathbf 1$ (the bit false, resp. true). The characters are $\chi_\varnothing\equiv 1$ and $\chi_{\{0\}}(\mathbf 0)=1$, $\chi_{\{0\}}(\mathbf 1)=-1$. Hence $g$ itself takes the values
\[
g(\mathbf 0)=a+b,\qquad g(\mathbf 1)=a-b,
\]
which is exactly the content of the two one-bit evaluation identities (`one_bit_val_false`, `one_bit_val_true`). Reading the definition of $T_\rho$ off its spectral formula, the sum over $S$ has just two terms, $\rho^0 a\,\chi_\varnothing$ and $\rho^1 b\,\chi_{\{0\}}$, so
\[
T_\rho g(\mathbf 0)=a+\rho b,\qquad T_\rho g(\mathbf 1)=a-\rho b.
\]
Since the factor $\tfrac12$ is common to both sides and $t\mapsto t^{1/q}$ is increasing (as $q>0$), the claimed inequality is equivalent to the single scalar statement
\[
|a+\rho b|^{q}+|a-\rho b|^{q}\;\le\;|a+b|^{q}+|a-b|^{q}. \tag{$\star$}
\]
The rest of the proof establishes $(\star)$ for arbitrary reals $a,b$; it is the lemma's one nontrivial ingredient.

2. **The arguments as convex combinations.** The key algebraic observation is that each noised value is a convex combination of the two un-noised ones. Indeed, with weights $\lambda_{+}=\tfrac{1+\rho}{2}$ and $\lambda_{-}=\tfrac{1-\rho}{2}$ — both nonnegative because $0\le\rho\le1$, and summing to $1$ —
\[
a+\rho b=\lambda_{+}(a+b)+\lambda_{-}(a-b),\qquad
a-\rho b=\lambda_{+}(a-b)+\lambda_{-}(a+b).
\]
(Expand the right-hand sides: the $a$-terms give $a$, the $b$-terms give $\pm\rho b$.) By the triangle inequality applied to these convex combinations,
\[
|a+\rho b|\le \lambda_{+}|a+b|+\lambda_{-}|a-b|,\qquad
|a-\rho b|\le \lambda_{+}|a-b|+\lambda_{-}|a+b|.
\]

3. **Convexity of $t\mapsto t^{q}$.** For $q\ge1$ the power function is convex on $[0,\infty)$ (`convexOn_rpow`). Applying Jensen's inequality with the weights $\lambda_{+},\lambda_{-}$ to the nonnegative numbers appearing above, and using that $t\mapsto t^{q}$ is monotone on $[0,\infty)$ so the bounds of Step 2 may be raised to the $q$-th power, we get
\[
|a+\rho b|^{q}\le\bigl(\lambda_{+}|a+b|+\lambda_{-}|a-b|\bigr)^{q}\le\lambda_{+}|a+b|^{q}+\lambda_{-}|a-b|^{q},
\]
\[
|a-\rho b|^{q}\le\bigl(\lambda_{+}|a-b|+\lambda_{-}|a+b|\bigr)^{q}\le\lambda_{+}|a-b|^{q}+\lambda_{-}|a+b|^{q}.
\]

4. **Adding and cancelling the weights.** Summing the two displays, the coefficient of $|a+b|^{q}$ is $\lambda_{+}+\lambda_{-}=1$, and likewise for $|a-b|^{q}$. Thus
\[
|a+\rho b|^{q}+|a-\rho b|^{q}\le |a+b|^{q}+|a-b|^{q},
\]
which is precisely $(\star)$.

5. **Conclusion.** Substituting $g(\mathbf 0)=a+b$, $g(\mathbf 1)=a-b$, $T_\rho g(\mathbf 0)=a+\rho b$, $T_\rho g(\mathbf 1)=a-\rho b$ into $(\star)$ and multiplying by $\tfrac12$ gives $\mathbb{E}\,|T_\rho g|^q\le\mathbb{E}\,|g|^q$. Both sides are nonnegative, so raising to the power $1/q$ — a monotone operation since $q>0$ (`Real.rpow_le_rpow`) — yields the stated bound $\bigl(\mathbb{E}\,|T_\rho g|^q\bigr)^{1/q}\le\bigl(\mathbb{E}\,|g|^q\bigr)^{1/q}$. $\qquad\blacksquare$

**Key facts.** `BooleanAnalysis.Hypercontractivity.one_bit_val_false`, `BooleanAnalysis.Hypercontractivity.one_bit_val_true`.
