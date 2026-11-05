<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.foldl_rho_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Stability of a Restriction Fold at an Untouched Variable

**Claim.** Fix $n$ and a term $t$ over $n$ variables, i.e. a list of literals. Let $\rho_0 : \mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$ be a restriction, $v \in \mathrm{Fin}\,n$ a variable, and $(k_1,b_1),\dots,(k_m,b_m)$ a list of entries. Process the entries left to right from $\rho_0$: for $(k_i,b_i)$, drop the first $k_i$ literals of $t$; if the remainder is nonempty with head literal $l$, reassign the variable of $l$ the value $b_i$, and otherwise leave the restriction unchanged. Suppose no entry touches $v$: for each $(k_i,b_i)$, whenever dropping the first $k_i$ literals of $t$ leaves a head literal $l$, the variable of $l$ is not $v$. Then the restriction produced after processing every entry assigns $v$ exactly the value $\rho_0$ assigns it.

**Proof.** The argument is a straightforward left-to-right induction on the list of entries, and the whole point is that each update step either does nothing or writes to a variable other than $v$, so the value stored at $v$ is never disturbed.

We induct on the list of entries, **generalizing the starting restriction** $\rho_0$. Generalizing is essential: the fold hands each successive step a restriction that may already have been modified, so the induction hypothesis must speak about an arbitrary starting restriction, not the fixed original.

1. **Empty list.** With no entries to process, the fold returns its seed $\rho_0$ unchanged, and the claim $\rho_0\,v = \rho_0\,v$ is immediate.

2. **One entry $(k,b)$ followed by the rest.** Peeling off the first step of the fold, the restriction fed to the remaining steps is
   \[
   \rho_1 \;=\;
   \begin{cases}
   \rho_0, & \text{if } \mathrm{drop}_k(t) = [\,], \\[2pt]
   \rho_0 \text{ with the variable of } l \text{ reset to } b, & \text{if } \mathrm{drop}_k(t) = l :: \mathit{rest}.
   \end{cases}
   \]
   The non-touching hypothesis, restricted to the tail of the entry list, lets the induction hypothesis apply to $\rho_1$: processing the remaining entries from $\rho_1$ assigns $v$ the value $\rho_1\,v$. So it suffices to show $\rho_1\,v = \rho_0\,v$, and we split on the two cases above.

3. **The dropped remainder is empty.** Here $\rho_1 = \rho_0$, so there is nothing to prove; the induction hypothesis on the tail finishes it directly.

4. **The dropped remainder has head literal $l$.** Now $\rho_1$ is $\rho_0$ pointwise, except at the variable of $l$, where it holds $b$. Evaluating a single-point update at $v$ gives
   \[
   \rho_1\,v \;=\;
   \begin{cases}
   b, & \text{if } v = \mathrm{var}(l), \\
   \rho_0\,v, & \text{otherwise}
   \end{cases}
   \]
   (the defining equation of `Function.update`). The non-touching hypothesis applied to this very entry — using exactly the fact that $\mathrm{drop}_k(t) = l :: \mathit{rest}$ — tells us $\mathrm{var}(l) \ne v$. Hence the first branch is impossible, the update is invisible at $v$, and $\rho_1\,v = \rho_0\,v$, as required.

In both cases the single step preserves the value at $v$, and the induction hypothesis carries that preservation through the rest of the list.
