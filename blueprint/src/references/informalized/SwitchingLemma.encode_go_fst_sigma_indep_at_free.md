<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.encode_go_fst_sigma_indep_at_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Free-variable output of the Razborov encoder is start-independent

**Claim.** Fix a DNF formula $f$ on $n$ variables, a width $w$, a fuel bound, a decision path (a list of variable–direction pairs), and a base restriction $\rho_0$. Run the recursive worker of the Razborov encoding on these inputs together with a running restriction $\sigma$ and empty auxiliary data, and write $R(\sigma)$ for the restriction that appears as the worker's first output. If a variable $v$ is left free by $\rho_0$ and by two running restrictions $\sigma_1$ and $\sigma_2$ — that is, $\rho_0(v)$, $\sigma_1(v)$ and $\sigma_2(v)$ are all undefined — then the two runs agree at $v$: $R(\sigma_1)(v) = R(\sigma_2)(v)$. In words, at a variable the base restriction leaves free, the worker's output restriction does not depend on which free-at-$v$ running restriction it was started from.

**Proof.** The argument is an induction on the fuel bound, with the path, the base restriction $\rho_0$, and *both* running restrictions $\sigma_1,\sigma_2$ generalized — the point of generalizing $\sigma_1,\sigma_2$ is that the inductive hypothesis will be re-applied not at $\sigma_1,\sigma_2$ themselves but at the running restrictions produced one layer down.

1. **Terminal cases.** If the fuel is exhausted, or the decision path is empty, or either of the worker's two early-termination guards fires, the worker stops and returns its running restriction unchanged as its first component. In each of these cases $R(\sigma_i)(v) = \sigma_i(v)$, and since $\sigma_1(v)=\sigma_2(v)=\text{undefined}$ by hypothesis, both sides are undefined and the equality holds.

2. **Recursive case: the one step the worker takes.** Otherwise the fuel is $m+1$, the path is $\text{step}::\text{rest}$, and the current DNF term is a nonempty literal list $\ell::\ell s$. The worker processes this clause's literals by `processClauseLits`, which returns a quadruple $(\pi',\ \rho',\ \sigma'_i,\ a'_i)$ — a new path, a new base restriction, a new running restriction, and new auxiliary data — and then recurses on fuel $m$ with these. The key structural fact is that only the running restriction (and the auxiliary data) can depend on the *input* running restriction: the new path $\pi'$ and the new base restriction $\rho'$ are literally the same whether processing starts from $\sigma_1$ or from $\sigma_2$ (processClauseLits is $\sigma$-independent in its first two outputs, `processClauseLits_sigma_indep`).

3. **Discarding the accumulator and aligning the common data.** The worker's first output component does not depend on its accumulator (`encode_go_fst_acc`), so the auxiliary data $a'_1,a'_2$ threaded into the two recursive calls can be replaced by the empty list — which is exactly the accumulator the lemma (and hence the inductive hypothesis) fixes. Using Step 2, the two recursive calls now run on a *common* path $\pi'$ and a *common* base restriction $\rho'$, differing only in the running restriction: the left-hand side carries $\sigma'_1$, the right-hand side $\sigma'_2$. We have reduced the goal to \[ R(\sigma'_1)(v) = R(\sigma'_2)(v) \] at fuel $m$, over the same $\pi'$ and $\rho'$.

4. **Dichotomy on whether $v$ survives as free.** Whether the inductive hypothesis applies turns on $\rho'(v)$.

   - **Case A: $\rho'(v)$ is undefined.** Then $v$ is still free under the new base restriction. When $v$ is free under both $\rho_0$ and $\rho'$, processing the clause leaves the running restriction at $v$ untouched: $\sigma'_i(v) = \sigma_i(v)$ (`processClauseLits_sigma_none_of_rho_none`), which is undefined by hypothesis. Thus $v$ is free under $\rho'$, $\sigma'_1$ and $\sigma'_2$ — precisely the three freeness hypotheses the lemma asks for, now at fuel $m$. The inductive hypothesis gives $R(\sigma'_1)(v) = R(\sigma'_2)(v)$, which is the goal.

   - **Case B: $\rho'(v)$ is defined.** Then $v$ is no longer free under the base restriction (processing the clause has fixed it). At a variable the base restriction fixes, the worker's first output simply equals its running restriction there (`encode_go_fst_nonfree`), so $R(\sigma'_i)(v) = \sigma'_i(v)$. It remains to compare $\sigma'_1(v)$ and $\sigma'_2(v)$. Since $\sigma_1(v)=\sigma_2(v)$ (both undefined), clause processing preserves agreement of the running restriction at $v$ (`processClauseLits_sigma_at_v`), so $\sigma'_1(v)=\sigma'_2(v)$ and the two sides coincide.

In both cases the equality at fuel $m+1$ follows, completing the induction.

**Key facts.** `SwitchingLemma.processClauseLits_sigma_indep`, `SwitchingLemma.encode_go_fst_acc`, `SwitchingLemma.processClauseLits_sigma_none_of_rho_none`, `SwitchingLemma.encode_go_fst_nonfree`, `SwitchingLemma.processClauseLits_sigma_at_v`.
