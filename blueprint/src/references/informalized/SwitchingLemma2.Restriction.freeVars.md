<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Restriction.freeVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The free coordinates of a restriction

**Definition.** A restriction is `Restriction n := Fin n → Option Bool` (an
`abbrev`): each coordinate is either fixed to a bit (`some b`) or left free
(`none`, the usual `⋆`). Its free-variable set is

`freeVars ρ : Finset (Fin n) := Finset.univ.filter (fun i => (ρ i).isNone)`,

the coordinates where `ρ` is `none`. No proof is involved — this is a plain
definition.

**Remark.** The file immediately derives `numFree ρ := ρ.freeVars.card` and
`IsRestriction s ρ := (ρ.numFree = s)`, so `freeVars` is the single place where
"free" is pinned down; every counting argument in the switching-lemma
development goes through its cardinality.

**Used in.** `numFree` and hence `IsRestriction` (same file), and directly in
`Switching/CanonicalDTree.lean`, `Switching/Encoding.lean`,
`Switching/EncodingProperties.lean`, `Switching/RoundTrip.lean`,
`Switching/BernoulliRestriction.lean`, and the `LMN/` restriction files.
