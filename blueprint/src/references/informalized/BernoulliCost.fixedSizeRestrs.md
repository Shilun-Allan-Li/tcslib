<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: fixedSizeRestrs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The restrictions on `n` variables with exactly `k` free variables

**Definition.** `fixedSizeRestrs n k : Finset (Restriction n)` is the finite set
of restrictions `ρ : Fin n → Option Bool` whose free-variable set has size
exactly `k`, i.e. `Finset.univ.filter (fun ρ => ρ.freeVars.card = k)`. Here
`ρ.freeVars` is the set of coordinates where `ρ` is `none` (the `⋆` positions),
so `fixedSizeRestrs n k` is the support of the fixed-size restriction model
`R_k`.

**Remark.** Its cardinality is `C(n,k) · 2^(n−k)` — choose which `k` coordinates
are starred, then assign a bit to each of the remaining `n − k`. That count is
established inline as the first `have` of `bernoulli_decompose` rather than as a
standalone lemma.

**Used in.** `fixedSizeRestrProb`, and through it every statement in the file.
