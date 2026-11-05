<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_rho_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Processing a Clause Never Frees a Fixed Variable

**Claim.** Fix $n$ and work with restrictions on $n$ variables, i.e. maps $\mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$, where a variable is *fixed* when its value is some $\mathrm{some}\,b$ and *free* when it is $\mathrm{none}$. Let $\rho_0$ and $\sigma$ be two such restrictions, let $\ell$ be a list of literals each tagged with its clause-position index, and let a decision-tree path (a list of variable/direction pairs) be given. Running the clause-processing routine on these inputs returns an updated path, updated versions of $\rho_0$ and $\sigma$, and a list of accumulated index/direction pairs. The claim is that if a variable $v$ is fixed under $\rho_0$ — that is, $\rho_0(v) \neq \mathrm{none}$ — then $v$ is still fixed under the returned version of $\rho_0$. Processing a clause never turns a fixed variable back into a free one.

**Proof.** The routine $\mathrm{processClauseLits}$ consumes the literal list and the path in lockstep, and it is defined by recursion on both:

- If there are no literals left, it returns the inputs untouched: the path, $\rho_0$, $\sigma$, and an empty accumulator.
- If the path is exhausted (but literals remain), it returns the empty path, $\rho_0$, $\sigma$ unchanged, and an empty accumulator.
- Otherwise it peels off the leading literal $(\ell, \mathit{idx})$ and the leading path step $(\_, \mathit{dir})$, and recurses on the remaining literals and path, but with the two restrictions *overwritten at the variable* $\ell.\mathrm{var}$: $\rho_0$ is updated to take the value $\mathrm{some}\,\mathit{dir}$ there, and $\sigma$ to take the value $\mathrm{some}\,(\neg\,\ell.\mathrm{neg})$. The index/direction pair $(\mathit{idx},\mathit{dir})$ is then pushed onto the accumulator returned by the recursive call.

The returned $\rho_0$ is the second component of the output 4-tuple. The whole argument rests on a single observation: every modification the routine ever makes to $\rho_0$ writes a value of the form $\mathrm{some}\,\mathit{dir}$ — never $\mathrm{none}$. So fixedness can only be created, never destroyed. (The parallel updates to $\sigma$ play no role here; the claim concerns $\rho_0$ alone, and $\sigma$ is merely carried along.) We make this precise by induction on the literal list $\ell$, keeping the path, $\rho_0$, and $\sigma$ universally quantified so that the induction hypothesis may be re-applied to the shortened path and the *updated* restrictions produced at each step.

1. **No literals left.** Here the routine returns $\rho_0$ verbatim, so the returned restriction's value at $v$ is exactly $\rho_0(v)$, which is $\neq \mathrm{none}$ by hypothesis.

2. **Literals remain but the path is empty.** Again the routine returns $\rho_0$ unchanged, and the hypothesis $\rho_0(v) \neq \mathrm{none}$ settles it directly.

3. **Both a literal $(\ell,\mathit{idx})$ and a path step $(\_,\mathit{dir})$ are present.** Unfolding one step of the recursion, the returned version of $\rho_0$ is precisely the one produced by the recursive call — a call whose starting restriction is $\rho_0$ overwritten at $\ell.\mathrm{var}$ with $\mathrm{some}\,\mathit{dir}$. Call this updated restriction $\rho_0'$. The induction hypothesis applies to the recursive call and tells us: if $\rho_0'(v) \neq \mathrm{none}$, then $v$ stays fixed in the final output. So it remains only to check $\rho_0'(v) \neq \mathrm{none}$. Reading off the pointwise definition of an updated function, there are two cases. If $v = \ell.\mathrm{var}$, then $\rho_0'(v) = \mathrm{some}\,\mathit{dir}$, which is certainly not $\mathrm{none}$. If $v \neq \ell.\mathrm{var}$, then the overwrite misses $v$ and $\rho_0'(v) = \rho_0(v)$, which is $\neq \mathrm{none}$ by the hypothesis. Either way $\rho_0'(v) \neq \mathrm{none}$, and the induction hypothesis finishes the step.

This completes the induction. The one external fact used is the pointwise behaviour of a single-point function override (`Function.update_apply`): updating a function at one argument changes its value only there. Everything else is unfolding the definition of the routine.

**Caveat.** The lemma listed under `upstream` (`SwitchingLemma.encode_go_fst_acc`) is not invoked by this proof; the argument depends only on the pointwise rule for function overrides (Mathlib's `Function.update_apply`) and on unfolding the definition of the routine, so `key_facts` is empty.
