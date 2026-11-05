<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_sigma_ne_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Processing literals preserves a non-negating restriction value

**Claim.** Fix a literal $\ell$ with variable $v = \mathrm{var}(\ell)$ and negation flag $b = \mathrm{neg}(\ell)$, two restrictions $\rho_0, \sigma$ on $n$ variables, and a list $\mathit{lits}$ of literals (each carrying its position index in the clause) that is run in lockstep against a decision-tree path. Suppose every literal occurring in $\mathit{lits}$ whose variable is $v$ is in fact equal to $\ell$, and suppose $\sigma$ does not already pin $v$ to the fixed value $b$, i.e. $\sigma(v) \neq \mathrm{some}\,b$. Let $\sigma'$ be the $\sigma$-component of the result of processing $\mathit{lits}$ against the path, starting from $\rho_0$ and $\sigma$. Then $\sigma'$ still does not pin $v$ to $b$: $\sigma'(v) \neq \mathrm{some}\,b$.

**Proof.** **Setup.** Recall how the procedure runs: it consumes the list of (literal, index) pairs and the path simultaneously. On the step headed by a literal $m$ and a path direction $\mathit{dir}$, it updates $\rho_0$ by setting $\mathrm{var}(m) \mapsto \mathrm{some}\,\mathit{dir}$, updates $\sigma$ by setting $\mathrm{var}(m) \mapsto \mathrm{some}(\neg\,\mathrm{neg}(m))$ — i.e. it fixes that variable to the value that *satisfies* the literal $m$ — and then recurses on the two tails. It halts, returning its inputs untouched, as soon as either the literal list or the path is empty. The $\sigma'$ of the statement is the accumulated $\sigma$ produced this way.

The whole content of the lemma is that the invariant "$\sigma(v) \neq \mathrm{some}\,b$" survives every such update. The argument is an induction on $\mathit{lits}$, carried out with the path and **both** restrictions $\rho_0, \sigma$ left general; this generality is essential, since each recursive call is made with a shorter path and with freshly updated restrictions.

1. **The list is exhausted.** If $\mathit{lits}$ is empty, the procedure returns its inputs verbatim, so $\sigma' = \sigma$, and the goal $\sigma'(v) \neq \mathrm{some}\,b$ is literally the hypothesis $\sigma(v) \neq \mathrm{some}\,b$.

2. **The path is exhausted.** If the list is nonempty but the path is empty, the procedure again halts immediately with $\sigma' = \sigma$, and the same hypothesis closes the goal.

3. **One processing step.** Otherwise $\mathit{lits} = (m, \mathit{idx}) :: \mathit{rest}$ and the path is $(\_, \mathit{dir}) :: \mathit{restPath}$. The procedure replaces $\sigma$ by
\[
\tilde\sigma \;=\; \sigma\big[\,\mathrm{var}(m) \mapsto \mathrm{some}(\neg\,\mathrm{neg}(m))\,\big]
\]
(and $\rho_0$ by an analogous update, which plays no role here), then recurses on $\mathit{rest}$ and $\mathit{restPath}$; the resulting $\sigma$-component is exactly our $\sigma'$. By the induction hypothesis, applied with the shorter list $\mathit{rest}$, the path $\mathit{restPath}$, and the restrictions $\tilde\sigma$ (together with the updated $\rho_0$), it suffices to verify the two premises of the hypothesis for this smaller instance.

   - *The equal-to-$\ell$ condition passes to $\mathit{rest}$.* Any literal appearing in $\mathit{rest}$ also appears in $\mathit{lits}$, so the assumption that every $v$-literal in $\mathit{lits}$ equals $\ell$ restricts straight away to $\mathit{rest}$.

   - *The invariant survives the update, i.e. $\tilde\sigma(v) \neq \mathrm{some}\,b$.* Split on whether the updated variable $\mathrm{var}(m)$ is our variable $v$.
     - If $\mathrm{var}(m) = v$, then $m$ is a literal of $\mathit{lits}$ with variable $v$, so by hypothesis $m = \ell$; in particular $\mathrm{neg}(m) = b$. The update therefore sets $\tilde\sigma(v) = \mathrm{some}(\neg b)$. Since $\neg b \neq b$ for every Boolean $b$ (and $\mathrm{some}$ is injective), $\mathrm{some}(\neg b) \neq \mathrm{some}\,b$, as required.
     - If $\mathrm{var}(m) \neq v$, the update touches a different coordinate, so $\tilde\sigma(v) = \sigma(v)$, and the original hypothesis $\sigma(v) \neq \mathrm{some}\,b$ carries over unchanged.

   In both subcases the induction hypothesis applies and yields $\sigma'(v) \neq \mathrm{some}\,b$, completing the step and the induction. $\qed$
