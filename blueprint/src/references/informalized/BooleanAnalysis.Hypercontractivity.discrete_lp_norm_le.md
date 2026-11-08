<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Discrete.lean :: BooleanAnalysis.Hypercontractivity.discrete_lp_norm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Higher Norm from Minimum Atom Mass

**Claim.** For a measurable random variable supported almost everywhere on a finite set whose atoms each have mass at least $\lambda>0$, its real-valued $L^q$ norm is at most $(1/\lambda)^{1/2-1/q}$ times its real-valued $L^2$ norm, for $q>2$.

**Proof.** Choose a finite set $s$ containing the values of $X$ almost everywhere, with each value in $s$ having mass at least $\lambda$. First, finite support implies $X\in L^2$; write $N=\|X\|_2$ and $L=\lambda$ viewed as an extended nonnegative real. On the level set where $X=X(\omega)$, the value $|X(\omega)|$ is constant. The lower bound on the mass of this level set, together with the lower bound of the $L^2$ norm by the contribution from any measurable set, gives almost everywhere $|X(\omega)|\,L^{1/2}\le N$. Thus $|X|\le N/L^{1/2}$ almost everywhere.

Raise this pointwise bound to the power $q-2$, multiply by $|X|^2$, and integrate. This yields
\[
\int |X|^q\,d\mu\le (N/L^{1/2})^{q-2}\int |X|^2\,d\mu.
\]
The $L^2$ integral equals $N^2$, so taking the $q$th root gives $\|X\|_q\le L^{-(1/2-1/q)}N$. Since $L=\lambda$, converting the extended norms to their real values gives the stated inequality.
