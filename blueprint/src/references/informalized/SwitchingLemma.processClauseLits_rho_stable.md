<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_rho_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Processing fixes $\rho_0$ outside the clause's variables

**Claim.** Fix $n$, a list $\mathrm{lits}$ of literals on $n$ variables each tagged with a position index, and a list $\mathrm{path}$ of variable–direction pairs. Starting from restrictions $\rho_0,\sigma$ on $n$ variables, let $\rho_0'$ be the restriction returned (as the second output component) by processing the free literals of $\mathrm{lits}$ against $\mathrm{path}$. If a variable $v$ is distinct from the variable of every literal occurring in $\mathrm{lits}$, then $\rho_0'(v)=\rho_0(v)$: the processing leaves $v$ exactly as it found it.

**Proof.** The point is simply that the restriction returned in the second slot is obtained from $\rho_0$ by a finite sequence of pointwise overwrites, each at the variable of some literal of $\mathrm{lits}$, and $v$ is none of those variables. We make this precise by following the recursion of the processing function, which marches down $\mathrm{lits}$ and $\mathrm{path}$ in lockstep. The argument is an induction on $\mathrm{lits}$, with $\mathrm{path}$, $\rho_0$ and $\sigma$ left general so that the inductive hypothesis may be re-used with the overwritten restrictions.

1. **Empty clause.** If $\mathrm{lits}$ is empty, processing returns $(\mathrm{path},\rho_0,\sigma,[\,])$ unchanged; the second component is $\rho_0$ itself, so the claim reads $\rho_0(v)=\rho_0(v)$.

2. **Exhausted path.** If $\mathrm{lits} = (l,\mathrm{idx})::\mathrm{restLits}$ but $\mathrm{path}$ is empty, the recursion bottoms out at $([\,],\rho_0,\sigma,[\,])$; again the second component is $\rho_0$, and there is nothing to prove.

3. **Recursive step.** Otherwise $\mathrm{lits}=(l,\mathrm{idx})::\mathrm{restLits}$ and $\mathrm{path}=(\_,\mathrm{dir})::\mathrm{restPath}$. By definition the output is formed by recursing on $\mathrm{restLits}$ and $\mathrm{restPath}$ from the *updated* restrictions
\[
\rho_0^{\ast} := \rho_0[\,l.\mathrm{var}\mapsto \mathrm{some}\ \mathrm{dir}\,],\qquad
\sigma^{\ast} := \sigma[\,l.\mathrm{var}\mapsto \mathrm{some}\ (\neg\, l.\mathrm{neg})\,],
\]
and the second component of the whole output is precisely the second component of that recursive call. Now $v$ avoids the variable of *every* literal of $\mathrm{lits}$, hence in particular $l.\mathrm{var}\neq v$, and $v$ also avoids the variables of all literals of $\mathrm{restLits}$. The latter observation lets us invoke the inductive hypothesis on $\mathrm{restLits}$, $\mathrm{restPath}$, $\rho_0^{\ast}$, $\sigma^{\ast}$: the recursive output agrees with $\rho_0^{\ast}$ at $v$, i.e. the second component evaluated at $v$ equals $\rho_0^{\ast}(v)$.

4. **Reading off the overwrite.** It remains to evaluate $\rho_0^{\ast}(v)=\rho_0[\,l.\mathrm{var}\mapsto \mathrm{some}\ \mathrm{dir}\,](v)$. A pointwise update changes the function only at the updated argument, so since $v\neq l.\mathrm{var}$ this value is just $\rho_0(v)$. Combining with the previous step, $\rho_0'(v)=\rho_0^{\ast}(v)=\rho_0(v)$, which is the assertion.
