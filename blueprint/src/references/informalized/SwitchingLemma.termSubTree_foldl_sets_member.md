<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: SwitchingLemma.termSubTree_foldl_sets_member -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Folding Literals Fixes Every Initially Free Variable

**Claim.** Fix $n$ variables, a Boolean assignment $x : \mathrm{Fin}\,n \to \mathrm{Bool}$, a starting restriction $\rho : \mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$, and a list of literals $\ell_1,\dots,\ell_m$. Process the literals left to right, carrying a current restriction that begins as $\rho$: on reaching a literal $\ell$, if its variable $\ell.\mathrm{var}$ is free in the current restriction, fix that variable to $x(\ell.\mathrm{var})$; otherwise leave the restriction alone. Let $\rho^*$ be the restriction left when the list is exhausted. Then for every literal $\ell$ occurring in the list whose variable is free in the original $\rho$, the entry $\rho^*(\ell.\mathrm{var})$ is defined (not $\mathrm{none}$); that is, $\ell.\mathrm{var}$ is no longer free in $\rho^*$.

**Proof.** Throughout, a restriction $\sigma$ has $\sigma(v) = \mathrm{none}$ exactly when $v$ is *free* in $\sigma$, and $\mathrm{freeVars}(\sigma)$ is the set of such $v$. One step of the fold sends a restriction $\sigma$ and a literal $\mathrm{lit}$ to
\[
\mathrm{step}(\sigma,\mathrm{lit}) \;=\;
\begin{cases}
\sigma[\mathrm{lit}.\mathrm{var} \mapsto \mathrm{some}\,x(\mathrm{lit}.\mathrm{var})] & \text{if } \mathrm{lit}.\mathrm{var} \in \mathrm{freeVars}(\sigma),\\
\sigma & \text{otherwise,}
\end{cases}
\]
and $\rho^*$ is the result of folding $\mathrm{step}$ over the whole list starting from $\rho$.

The argument rests on one monotonicity fact: **folding never un-defines a variable**. Precisely, if $\sigma(v) \neq \mathrm{none}$, then after folding any list of literals starting from $\sigma$, the entry at $v$ is still $\neq \mathrm{none}$ (`termSubTree_foldl_preserves_nonnone`). This is intuitively clear — a single step either leaves $\sigma$ untouched or overwrites one variable with a $\mathrm{some}$ value, and neither can turn a defined entry into $\mathrm{none}$ — and it is what lets us "cash in" the moment a variable becomes set.

The proof is by induction on the list of literals, with the starting restriction $\rho$ left general so that the inductive hypothesis may be instantiated at a *different* restriction than the one we began with.

1. **Empty list.** There is no literal $\ell$ in the empty list, so the hypothesis $\ell \in \mathrm{lits}$ is vacuously impossible and there is nothing to prove.

2. **Non-empty list $\mathrm{hd} :: \mathrm{tl}$.** Folding over $\mathrm{hd}::\mathrm{tl}$ from $\rho$ equals folding over $\mathrm{tl}$ from the once-stepped restriction $\rho_1 := \mathrm{step}(\rho,\mathrm{hd})$. We are given a literal $\ell$ with $\ell.\mathrm{var}$ free in $\rho$, and we split on whether $\ell$ is the head or lies in the tail.

3. **Case $\ell = \mathrm{hd}$.** Since $\ell.\mathrm{var}$ is free in $\rho$, the head step fires: $\rho_1 = \rho[\ell.\mathrm{var} \mapsto \mathrm{some}\,x(\ell.\mathrm{var})]$, so $\rho_1(\ell.\mathrm{var}) = \mathrm{some}\,x(\ell.\mathrm{var}) \neq \mathrm{none}$. The variable is now defined in $\rho_1$, and by the monotonicity fact the remaining fold over $\mathrm{tl}$ keeps it defined. Hence $\rho^*(\ell.\mathrm{var}) \neq \mathrm{none}$.

4. **Case $\ell \in \mathrm{tl}$.** Here we must understand $\rho_1$ before invoking the inductive hypothesis on $\mathrm{tl}$, so we split on whether the head step fired.

   - *The head step did not fire* ($\mathrm{hd}.\mathrm{var} \notin \mathrm{freeVars}(\rho)$). Then $\rho_1 = \rho$, and $\ell.\mathrm{var}$ is still free in $\rho_1 = \rho$. Applying the inductive hypothesis to the list $\mathrm{tl}$ started from $\rho$ gives the claim directly.

   - *The head step fired* ($\mathrm{hd}.\mathrm{var} \in \mathrm{freeVars}(\rho)$), so $\rho_1 = \rho[\mathrm{hd}.\mathrm{var} \mapsto \mathrm{some}\,x(\mathrm{hd}.\mathrm{var})]$. Split on whether $\ell$ and $\mathrm{hd}$ share a variable.
     - If $\ell.\mathrm{var} = \mathrm{hd}.\mathrm{var}$, then the update set this very entry, so $\rho_1(\ell.\mathrm{var}) = \mathrm{some}\,x(\mathrm{hd}.\mathrm{var}) \neq \mathrm{none}$; the monotonicity fact carries this through the rest of the fold, giving $\rho^*(\ell.\mathrm{var}) \neq \mathrm{none}$.
     - If $\ell.\mathrm{var} \neq \mathrm{hd}.\mathrm{var}$, then updating the entry at $\mathrm{hd}.\mathrm{var}$ leaves the entry at $\ell.\mathrm{var}$ untouched, so $\rho_1(\ell.\mathrm{var}) = \rho(\ell.\mathrm{var}) = \mathrm{none}$; that is, $\ell.\mathrm{var}$ is still free in $\rho_1$. Now the inductive hypothesis applies to $\mathrm{tl}$ started from $\rho_1$, yielding the claim.

In every case the entry at $\ell.\mathrm{var}$ in $\rho^*$ is defined, which is exactly the statement. $\qquad\blacksquare$

**Key facts.** `SwitchingLemma.termSubTree_foldl_preserves_nonnone`.
