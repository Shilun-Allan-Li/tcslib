<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: SwitchingLemma.extend_update_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Fixing a Free Variable to Its Point Value Preserves the Extension

**Claim.** Let $\rho : \mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$ be a restriction on $n$ variables, where $\rho(i) = \mathrm{some}\,c$ records a variable fixed to $c$ and $\rho(i) = \mathrm{none}$ records a free variable. Let $x : \mathrm{Fin}\,n \to \mathrm{Bool}$ be a point, and let $v$ be a free variable of $\rho$ (so $\rho(v) = \mathrm{none}$) with $x(v) = b$. Form the updated restriction $\rho[v \mapsto b]$ that fixes $v$ to $b$ and agrees with $\rho$ everywhere else. Then $\rho[v \mapsto b]$ and $\rho$ have the same extension along $x$: the Boolean assignments $(\rho[v \mapsto b]).\mathrm{extend}\,x$ and $\rho.\mathrm{extend}\,x$ are equal.

**Proof.** Recall that the extension of a restriction $\sigma$ along the point $x$ is the Boolean assignment defined coordinatewise by
\[
(\sigma.\mathrm{extend}\,x)(i) \;=\; \begin{cases} c & \text{if } \sigma(i) = \mathrm{some}\,c,\\ x(i) & \text{if } \sigma(i) = \mathrm{none},\end{cases}
\]
that is, each coordinate keeps the value $\sigma$ fixes there, falling back to the point $x$ wherever $\sigma$ is free. Since both sides of the claimed equality are functions on $\mathrm{Fin}\,n$, it suffices to prove they agree at an arbitrary index $i$, and we split on whether $i$ is the updated variable $v$.

1. **Away from $v$ (the case $i \neq v$).** Updating $\rho$ at $v$ changes no other coordinate, so $\rho[v \mapsto b](i) = \rho(i)$. The two extensions therefore apply the identical case of the definition above at $i$ and return the same value. This coordinate carries no content.

2. **At $v$ (the case $i = v$).** Here the two sides are computed through different branches of the definition, yet land on the same Boolean. On one side, $\rho[v \mapsto b]$ fixes $v$ to $b$, i.e. $\rho[v \mapsto b](v) = \mathrm{some}\,b$, so its extension at $v$ is simply $b$. On the other side, the hypothesis that $v$ is a free variable of $\rho$ unfolds to exactly the statement $\rho(v) = \mathrm{none}$ (membership in $\mathrm{freeVars}(\rho)$ is, by definition, the condition that $\rho(v)$ is the empty option). Hence the extension of $\rho$ at $v$ falls back to the point value $x(v)$, which by hypothesis equals $b$. Both sides are therefore $b$, and they agree.

Having matched the two assignments at every index, they are equal as functions. $\qquad\blacksquare$

The argument is purely a definitional unfolding: the only hypotheses that do real work are $\rho(v) = \mathrm{none}$ (so that the pre-update extension genuinely consults $x$ at $v$) and $x(v) = b$ (so that the value it consults matches the value the update installs).
