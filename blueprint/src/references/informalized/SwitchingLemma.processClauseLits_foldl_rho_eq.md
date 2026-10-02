<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_foldl_rho_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's ρ₀-foldl reproduces the encoder's ρ₀

**Claim.** Fix a term `t` and a literal list `lits` contained in `t.zipIdx`, and
suppose the encoder's and decoder's restrictions agree at `v` to begin with
(`ρ₀ v = ρ₀_dec v`). Then replaying the aux block
`(processClauseLits lits path ρ₀ σ).2.2.2` through the decoder's ρ₀-update foldl
— `fun ρ₀ e => match t.drop e.1 with | [] => ρ₀ | l :: _ =>
Function.update ρ₀ l.var (some e.2)` — starting from `ρ₀_dec` gives exactly
`(processClauseLits lits path ρ₀ σ).2.1 v`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`, `ρ₀_dec`.

1. `lits = []`, and `lits = hd :: tl` with `path = []`: aux is `[]` and
   `pcl.2.1 = ρ₀`, so the goal is `hinit` — `simp [processClauseLits, hinit]`.
2. `lits = hd :: tl`, `path = p :: ps`: after
   `simp only [processClauseLits, List.foldl_cons]`, `zipIdx_drop_spec t hd.1 hd.2
   (hmem hd (.head _))` rewrites `t.drop hd.2` to `hd.1 :: drop_rest`. The
   decoder's first step is `Function.update ρ₀_dec hd.1.var (some p.2)`, matching
   the encoder's `Function.update ρ₀ hd.1.var (some p.2)`.
3. Apply `ih` at `ps` with those two updates; the refreshed agreement hypothesis
   is discharged by `simp only [Function.update_apply]; split <;> simp_all` (both
   sides get `some p.2` when `hd.1.var = v`, else both keep their old value).

**Used in.** `processClauseLits_foldl_rho_eq_of_set`, which reduces to this lemma
once the current literal has pinned `v` on both sides.
