<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: go_roundtrip_gen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Generalized round-trip for the encoder/decoder loops

**Claim.** Let `f` have width ≤ `w` and variable-distinct literals within each
clause (`hnd`), and set `enc := razborovEncode.go f w enc_fuel path ρ₀ σ []`.
Suppose the decoder is started from a state `(σ_dec, ρ₀_dec)` that is *consistent*
with the encoder's state: `σ` is free wherever `ρ₀` is (`hE`); `σ_dec` and `ρ₀_dec`
both agree with `enc.1` at every variable free in `ρ₀` (`hA`, `hB`); `σ_dec` agrees
with `σ` and `ρ₀_dec` with `ρ₀` at every variable fixed by `ρ₀` (`hC`, `hD`); and
`dec_fuel ≥ enc.2.length + 1`. Then
`(razborovDecode.go f w dec_fuel σ_dec ρ₀_dec enc.2).1 = σ`.

**Proof.** Induction on `enc_fuel`, generalizing `path`, `ρ₀`, `σ`, `σ_dec`, `ρ₀_dec`,
`dec_fuel`. A single `have base` handles every case where the encoder emits
nothing (`enc = (σ, [])`) by `roundtrip_base`, using `hA` and `hC`.

- *Trivial arms* — fuel `0`, empty path, `f.find? … = none`, or the chosen clause
  has no free literals: `simp only [razborovEncode.go]` reduces `enc` to `(σ, [])`,
  then `base`.
- *Main arm* — clause `t_clause` found (`split` / `rename_i`), free-literal list
  `generalize`d to `fl :: fls`, `pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ`
  and `rec_enc` the recursive encoder run:
  1. `encode_go_acc` gives `enc = (rec_enc.1, pcl.2.2.2 ++ [(w,false)] ++ rec_enc.2)`;
     hence `henc1_eq : enc.1 = rec_enc.1` and the aux split `haux`.
  2. The decoder finds the same clause (`find_clause_preserved_in_encode`), and its
     `processEntries` on that block replays the two `Function.update` folds and stops
     at the `(w,false)` marker (`processEntries_of_processClauseLits`); this needs
     `t_clause.length ≤ w` (`term_length_le_width` with `hw`). The block is nonempty
     (`List.exists_cons_of_ne_nil`) and `dec_fuel = df + 1`.
  3. `encode_go_snd_sigma_indep` replaces `rec_enc.2` by the aux output of the run
     started from `σ`, so the IH applies with the folded restrictions as decoder state.
  4. Side goals: `hE'` from `pcl_none_implies_rho_free`; `hC'`/`hD'` from
     `roundtrip_inv_hC'` / `roundtrip_inv_hD'`; `hA'`/`hB'` because the fold is inert
     at still-free `v` (`foldl_sigma_stable` / `foldl_rho_stable` via
     `processClauseLits_aux_ne_of_pcl_none`), then `hA`/`hB`, `henc1_eq` and
     `encode_go_fst_sigma_indep_at_free`; the fuel bound by `omega` from `haux`; and
     the remaining `base` obligation by `roundtrip_base` plus a `calc` chain through
     the same four rewrites.
