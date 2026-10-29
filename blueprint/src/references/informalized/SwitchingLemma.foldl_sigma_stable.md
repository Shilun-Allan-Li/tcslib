<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.foldl_sigma_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Variable-freeing folds fix untargeted variables

**Claim.** Fix a term $t$ (a list of literals) over $n$ variables, a restriction $\sigma : \mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$, a variable $v$, and a finite list of entries, each a pair $(k,b)$. Process the entries left to right starting from $\sigma$: for an entry $(k,b)$, drop the first $k$ literals of $t$; if nothing remains, keep the current restriction, and otherwise free (set to unassigned) the variable of the first remaining literal $l$. Assume that for every entry $(k,b)$, whenever dropping the first $k$ literals of $t$ leaves a nonempty list with first literal $l$, the variable of $l$ differs from $v$. Then the restriction produced after all entries have been processed agrees with $\sigma$ at $v$.

**Proof.** The argument is a straightforward induction on the list of entries, but with one essential twist: the induction is carried out *with the starting restriction left general*, so that the inductive hypothesis may be applied to a modified restriction rather than only to $\sigma$ itself.

1. **Base case (no entries).** The fold over the empty list returns the starting restriction unchanged, so its value at $v$ is literally $\sigma(v)$.

2. **Inductive step: peel off the first entry.** Suppose the list is $e :: es$ with $e = (k,b)$, and assume the statement holds for the tail $es$ *for every starting restriction*. Processing $e :: es$ from $\sigma$ means first applying the update rule for $e$ to $\sigma$, obtaining some restriction $\sigma'$, and then folding the remaining entries $es$ starting from $\sigma'$. The hypothesis $\mathtt{hne}$ restricts to $e$ (giving the premise about this entry) and to each member of $es$ (giving the hypothesis needed to invoke the inductive claim on the tail).

3. **Split on whether $t$ runs out.** Examine $t.\mathrm{drop}\,k$, the term with its first $k$ literals removed.
   - **If it is empty**, the update rule leaves the restriction untouched, so $\sigma' = \sigma$, and processing $e :: es$ from $\sigma$ is the same as processing $es$ from $\sigma$. The inductive hypothesis (applied to the starting restriction $\sigma$) gives exactly $\sigma(v)$.
   - **If it is $l :: \mathit{rest}$** for some literal $l$, the update rule frees the variable of $l$, so $\sigma' = \sigma$ with the coordinate $\mathrm{var}(l)$ reset to unassigned (`Function.update` of $\sigma$ at $\mathrm{var}(l)$ to $\mathrm{none}$).

4. **Apply the induction hypothesis to the modified restriction.** This is where generality matters: the fold over $es$ now starts from $\sigma'$, not $\sigma$. Because the inductive hypothesis was proved for an arbitrary starting restriction, it applies to $\sigma'$ and reduces the value of the whole fold at $v$ to $\sigma'(v)$.

5. **Evaluate the freed restriction at $v$.** By definition of a pointwise update, $\sigma'(v)$ equals $\mathrm{none}$ if $v = \mathrm{var}(l)$ and $\sigma(v)$ otherwise (`Function.update_apply`). The premise of $\mathtt{hne}$ for the entry $e$, applied to the decomposition $t.\mathrm{drop}\,k = l :: \mathit{rest}$, says precisely that $\mathrm{var}(l) \neq v$; hence $v \neq \mathrm{var}(l)$, the conditional takes its second branch, and $\sigma'(v) = \sigma(v)$.

In both cases the value of the completed fold at $v$ is $\sigma(v)$, completing the induction. The Boolean component $b$ of each entry plays no role anywhere, as it is never consulted by the update rule.
