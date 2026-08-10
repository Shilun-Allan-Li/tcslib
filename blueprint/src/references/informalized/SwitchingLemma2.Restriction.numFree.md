<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Restriction.numFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The number of free coordinates of a restriction

**Definition.** For `ρ : Restriction n = Fin n → Option Bool`,

`numFree ρ : ℕ := ρ.freeVars.card`,

the cardinality of the free-variable set `freeVars ρ = Finset.univ.filter (fun i
=> (ρ i).isNone)`. A one-line plain definition; no proof.

**Remark.** This is the size parameter of the whole switching-lemma
development. The predicate `IsRestriction s ρ` in the same file is literally
`ρ.numFree = s`, and `numFree` also serves as the termination measure for the
canonical decision tree: `canonicalDTree` starts the recursion with fuel
`ρ.numFree + 1`, justified by `numFree_update_lt` (fixing a free coordinate
strictly decreases it).

**Used in.** `IsRestriction` (same file); `Switching/CanonicalDTree.lean`
(`numFree_update_lt`, `termSubTree_foldl_numFree_lt`, and the fuel invariant);
`Switching.lean`, where the Razborov encoder's accounting lemmas
(`numFree_update_free`, `processClauseLits_numFree_σ`,
`numFree_update_some_ge`) and the counting lemma `card_filter_numFree_eq` are
all phrased in it; and `LMN/SwitchingBernoulli.lean`.
