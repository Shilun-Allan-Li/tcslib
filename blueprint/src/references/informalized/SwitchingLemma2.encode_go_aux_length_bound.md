<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_aux_length_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Aux output length is at most twice the path length

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path : List (Fin n × Bool)`,
`ρ₀ σ : Restriction n` and `acc : List (ℕ × Bool)`,

```
(razborovEncode.go f w fuel path ρ₀ σ acc).2.length ≤ acc.length + 2 * path.length
```

i.e. each path step contributes at most two aux entries (one literal entry plus
its share of the `(w, false)` clause markers). Declared `private`.

**Proof.** Induction on `fuel`, generalizing `path`, `ρ₀`, `σ`, `acc`.

1. `fuel = 0` (both `path = []` and `path = _ :: _`): the loop returns
   `(σ, acc)`, so `simp [razborovEncode.go]`.
2. `fuel + 1`, `path = []`: same, `simp [razborovEncode.go]`.
3. `fuel + 1`, `path = step :: rest`: `simp only [razborovEncode.go]` and
   `split` twice — when `f.find?` yields `none`, or the free-literal filter is
   `[]`, the output is `acc` and `simp` closes it.
4. Recursive branch (`fl :: fls`): `apply le_trans (ih _ _ _ _)` to bound the
   recursive call by its own accumulator length plus twice the remaining path.
   Expand that accumulator with
   `simp only [List.length_append, List.length_cons, List.length_nil]`, feed in
   the tight one-clause estimate `processClauseLits_tight fl fls step rest ρ₀ σ`
   (aux entries `+ 1` marker `+ 2 ·` remaining path `≤ 2 * (step :: rest).length`)
   and `List.length_cons`, then `omega`.

**Used in.** `razborovEncode_aux_length_le`, which instantiates `acc = []` and
`path = (canonicalDTree f ρ).deepPath.take d` to get the `≤ 2 * d` bound on the
encoding used for the counting argument.
