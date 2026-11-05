<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_sigma_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Stability of the σ-restriction away from a clause's variables

**Claim.** Fix $n$ and consider the routine that processes a list $\mathrm{lits}$ of literals over $\mathrm{Fin}\,n$ (each tagged with a position index) against a list $\mathrm{path}$ of variable–direction pairs, starting from two restrictions $\rho_0$ and $\sigma$ (each a map $\mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$). Let $\sigma'$ be the restriction this routine returns. If a variable $v$ is the variable of no literal occurring in $\mathrm{lits}$, then $\sigma'$ is unchanged from $\sigma$ at $v$: $\sigma'(v) = \sigma(v)$.

**Proof.** Recall how the routine builds its output restriction $\sigma'$. It walks the two lists $\mathrm{lits}$ and $\mathrm{path}$ in lockstep. If either list is empty it stops and returns the current $\sigma$ untouched. Otherwise it takes the head literal $l$ (together with its index $\mathrm{idx}$) and the head direction $\mathrm{dir}$, overwrites $\sigma$ at the variable $l.\mathrm{var}$ with the value $\mathrm{some}(\lnot\, l.\mathrm{neg})$, correspondingly overwrites $\rho_0$ at $l.\mathrm{var}$ with $\mathrm{some}\,\mathrm{dir}$, and recurses on the two tails. Thus the only places where $\sigma$ is ever altered are the variables of the literals that are actually consumed — and each consumed literal certainly occurs in $\mathrm{lits}$. The point of the lemma is to confirm this: a variable touched by none of the literals is left exactly as it was.

The argument is an induction on the list $\mathrm{lits}$, with $\mathrm{path}$, $\rho_0$, and $\sigma$ all kept general so that the hypothesis is available at the updated restriction in the recursive step.

1. **Base case ($\mathrm{lits}$ empty).** The routine immediately returns its input $\sigma$, so $\sigma' = \sigma$ and in particular $\sigma'(v) = \sigma(v)$.

2. **Inductive step ($\mathrm{lits} = (l,\mathrm{idx}) :: \mathrm{restLits}$).** Split on $\mathrm{path}$.
   - If $\mathrm{path}$ is empty, the routine again returns $\sigma$ unchanged, so $\sigma'(v) = \sigma(v)$ outright.
   - If $\mathrm{path} = (\_,\mathrm{dir}) :: \mathrm{restPath}$, then by definition $\sigma'$ is the restriction produced by the recursive call on $\mathrm{restLits}$ and $\mathrm{restPath}$, starting from the updated pair $\bigl(\rho_0[l.\mathrm{var} \mapsto \mathrm{some}\,\mathrm{dir}],\ \sigma[l.\mathrm{var} \mapsto \mathrm{some}(\lnot\, l.\mathrm{neg})]\bigr)$. (The index $\mathrm{idx}$ is pushed onto a separate output list that does not affect the restriction, so it plays no role here.)

   The assumption that $v$ is the variable of no literal in $\mathrm{lits}$ passes to the tail $\mathrm{restLits}$, since every literal of $\mathrm{restLits}$ is also a literal of $\mathrm{lits}$. Applying the induction hypothesis to the recursive call — now with starting restriction $\sigma[l.\mathrm{var} \mapsto \mathrm{some}(\lnot\, l.\mathrm{neg})]$ in place of $\sigma$ — gives
   \[
   \sigma'(v) = \bigl(\sigma[l.\mathrm{var} \mapsto \mathrm{some}(\lnot\, l.\mathrm{neg})]\bigr)(v).
   \]
   Finally, the same assumption applied to the head literal $(l,\mathrm{idx})$, which does occur in $\mathrm{lits}$, yields $l.\mathrm{var} \neq v$. Hence the pointwise update at $l.\mathrm{var}$ does not disturb the value at $v$, and $\bigl(\sigma[l.\mathrm{var} \mapsto \cdots]\bigr)(v) = \sigma(v)$. Combining the two displayed equalities gives $\sigma'(v) = \sigma(v)$, completing the induction.
