# Readers to insert: the probe of bb1-sim (Deliverable 3, Q7's advance scope evidence)

Sub-agent `probe`, 2026-11-17 UTC. Probe base: T4's delivered head
`c90273fad3511ada7c9c1a53e1abdd8478237cee` (worktree branch `probe/bb1-sim-readers`). There,
`IdentityBased/Defs.lean` has SHA-256 `4e220ead…` (476 lines) and `IdentityBased/BonehBoyen.lean`
has `da875140…` (714 lines). Evidence: `evidence/subagents/probe/`; `NOTES.md` gives the order of
the runs.

## Summary

**The one reader of ruling Q7 is not enough, and neither are Q7(B)'s three.** Under the
development seals, T2's step M reads through **ten** readers: six in `Defs.lean` and four in
`BonehBoyen.lean`.
- All ten are theorems: no definition, no attribute.
- Each is proved owner-side by `rfl` or in one line.
- None needs a change to a definition.

With them, the consumer probe states and proves P-1 (all nine cases), P-2 (every row of the step-M
table) and P-3:
- natively and under devseal A and B, with 0 errors;
- every probe lemma depends only on `propext`, `Classical.choice` and `Quot.sound`.

Two obstructions decide the set. In both, the owners elaborate a term at a type that a sealed
consumer cannot see through.
1. **The game's oracles.** `sidImpl`'s typed readers (`sidImpl_init_none`, …) state their answers
   at the owner's types, and these are of three kinds:
   - in the `⊥` cases the answer is `zeroBits (S.outLens κ i)`, of the game's answer type;
   - in the other cases it is a string of the scheme's width (`S.encPP κ pp`, `decAnswer …`,
     `S.encCT κ c`);
   - in the `KeyGen` and `Challenge` sampling cases, the whole right side is a bind typed at
     `(Fin (…) → Bool) × σ`.

   A reader that casts the answer back (`oracleImpl_*_onSpec`'s form) serves the second kind and
   breaks the first. A reader that casts only the query serves the first and breaks the second.
   The sampling cases need their own readers. The whole-function form
   `sidImpl = oracleImpl (sidImpl · 0) …` fails earlier: `oracleImpl_*_onSpec` cannot be
   instantiated at `init := S.sidImpl b κ pp msk 0`, whose type is the handler type only through
   `inLens`/`outLens`.
2. **`bb1Scheme`'s parameters.**
   - A consumer cannot write `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` (T4), and cannot instantiate a
     binder `pp : (bb1Scheme G ℓ).PP κ` with a `Σ`-typed term.
   - The generated `simps` lemmas `bb1Scheme_setup`, `bb1Scheme_keyGen` and `bb1Scheme_enc` are
     typed at `Σ …`, at `Fin (ℓ.eval κ) → Bool` and at `Fin (G.wT.eval κ) → Bool`. They cannot
     be used at the game's types.
   - The ciphertexts cannot be compared with `bb1SimCt` by `congrArg`: `bb1SimCt_eq` reads
     `decodeT _ m` in `BilinearGroup _ ((bb1Scheme G ℓ).msgLen.eval κ)`, while `Encrypt` reads it
     in `BilinearGroup _ (G.wT.eval κ)`. So a word reader for `encCT` is needed after all, as for
     `encPP` and `encSK`.

**Consequence for the fill (no reader, but a design point).**
- No consumer can name the real parameters `⟨d, (g, g^α, g_2, h)⟩`.
- The probe therefore states P-2 for any `o : G → PP κ × MSK κ` that satisfies `RealReads`, which
  lists what the real handler reads from its parameters: the `encPP` word, the message space, the
  `KeyGen` key words and the `Encrypt` ciphertext words.
- It gets `o` and `RealReads` from the setup by an existential, `setup_out`:
  `∃ o, (∀ F, (Setup κ).bind F = (sample r).bind … fun g2 => F (o r g α h g2)) ∧ ∀ …, RealReads …`.
- The fill can use the same interface. This is design §3.3's "take the setup's output map as a
  parameter", with the map obtained by unification.

## 1. The minimal reader set

| # | Reader | Owner | Proof | Probe lemmas that use it |
|---|---|---|---|---|
| 1 | `IBEScheme.sidImpl_zero_onSpec` | `Defs.lean` | `(OracleComp.bind_pure _).symm` | `p1_init_none`, `p1_init_some` (so `p2_init_none`, `p2_init_some`) |
| 2 | `IBEScheme.sidImpl_two_onSpec` | `Defs.lean` | `(OracleComp.bind_pure _).symm` | `p1_challenge_repeat` (`p2_challenge_repeat`) |
| 3 | `IBEScheme.sidImpl_one_onQuery` | `Defs.lean` | `rfl` | `p1_keyGen_none`, `p1_keyGen_target` (`p2_keyGen_none`, `p2_keyGen_target`) |
| 4 | `IBEScheme.sidImpl_two_onQuery` | `Defs.lean` | `rfl` | `p1_challenge_none`, `p1_challenge_invalid` (`p2_challenge_none`, `p2_challenge_invalid`) |
| 5 | `IBEScheme.sidImpl_keyGen_ne_onSpec` | `Defs.lean` | `S.sidImpl_keyGen_ne …` | `p1_keyGen_ne` (`p2_keyGen_ne`) |
| 6 | `IBEScheme.sidImpl_challenge_fresh_onSpec` | `Defs.lean` | `S.sidImpl_challenge_fresh …` | `p1_challenge_fresh` (`p2_challenge_fresh`) |
| 7 | `bb1Scheme_setup_eq` | `BonehBoyen.lean` | `rfl` | `setup_out` |
| 8 | `bb1Scheme_keyGen_bind` | `BonehBoyen.lean` | `simp only [bb1Scheme_keyGen, …]` | `setup_out` (`RealReads.keyGen`, so `p2_keyGen_ne`) |
| 9 | `bb1Scheme_enc_bind` | `BonehBoyen.lean` | `rw [padFin_ofFn]; simp only [bb1Scheme_enc, …]` | `setup_out` (`RealReads.enc`, so `p2_challenge_fresh`) |
| 10 | `ofFn_bb1Scheme_encCT` | `BonehBoyen.lean` | `rfl` | `setup_out` (`RealReads.enc`, so `p2_challenge_fresh`) |

- **Names.**
  - None of the ten names occurs in `TCSlib/` or `audits/` at T4's head
    (`evidence/subagents/probe/clash/grep-worktree.tsv`, whole-word `grep`).
  - Declaring them in the readers probe raised no clash either. Its import closure contains
    `Defs` and `BonehBoyen` with their generated `simps` lemmas.
  - The formal scan at both bases is the lead's.
- **T4's readers used.**
  - `oracleImpl_{zero,one,two}_onSpec`: every simulator side of P-2, and P-3.
  - `ofFn_bb1Scheme_encPP`: `setup_out`, `p2_init_none`, `p2_init_some`.
  - `ofFn_bb1Scheme_encSK`: `setup_out`, `p2_keyGen_ne`.
  - `bb1Scheme_msgSpace_iff`: `setup_out`, `p2_challenge_invalid`, `p2_challenge_fresh`,
    `p3_challenge_fresh`.
  - `ofFn_bb1SimCt`: `p2_challenge_fresh`, `p3_challenge_fresh`.
- **Other published lemmas used:** `sidImpl_*`, `sidSpec_eq`, `bitSpec_dom`/`_rng`, `inLens_*`,
  `outLens_*`, `bb1SimImpl_eq`, `bb1SimInit_*`, `bb1SimKeyQ_*`, `bb1SimChal_*`, `bb1SimParams_eq`,
  `bb1SimKey_eq`, `BB1.F_eq`, `BB1.setup_eq`, `BB1.keyGen_eq`, `BB1.encrypt_eq`, `BB1.idToZ_eq`,
  and `OracleComp.pure_bind`/`bind_assoc`.
- **Type-level Rule 10.**
  - The probe's cast equations (`dom_zero`, …, `rng_two`) come from `sidSpec_eq`,
    `bitSpec_dom`/`_rng`, `inLens_*` and `outLens_*` only.
  - `zeroBits_eq_cast` uses `outLens_one`/`_two`.
  - The readers' own casts use `show … from rfl` owner-side, as T4's do.

## 2. Lean text and anchors (byte for byte)

Insert each block, preceded by one blank line, after its anchor line.
- The blank line and the docstring after the anchor stay unchanged.
- Add no import, `open`, attribute or other declaration.
- Leave the module docstrings alone (T4's precedent).

This was checked on copies of the two files at T4's head (`evidence/subagents/probe/insertion/`,
`tools/insert_check.py`):
- Each copy compiles natively, rc 0, 0 errors (`in-situ-native/`).
- Removing the block restores the base byte for byte.
- Results: `Defs.lean` 476 → **563** lines, SHA-256
  `97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0`; `BonehBoyen.lean`
  714 → **760** lines, SHA-256 `88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26`.
- Widths: at most 100 (`Defs` block) and 99 (`BonehBoyen` block) characters per line.

### 2.1 `IdentityBased/Defs.lean`: after line 430

Line 430 is `  (OracleComp.bind_pure _).symm`, the last line of `oracleImpl_two_onSpec`.
- The block goes before the docstring of `sidCodec`, inside `namespace IBEScheme`, and uses its
  `variable (S : IBEScheme)`.
- It has 86 lines; source: `insertion/Defs-block.lean.txt`.

```lean
/-- **Oracle `0` of the game on the game's query type**: `Init` on the query read as an identity,
its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 0 x s =
(S.sidImpl b κ pp msk 0 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_zero_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 0) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 0 x s =
      (S.sidImpl b κ pp msk 0
        (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of the game on the game's query type**: `Challenge` on the query read as two
messages, its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 2 x s =
(S.sidImpl b κ pp msk 2 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_two_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      (S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of the game, its query read as an identity**: the call on the game's query
type is the call on the query read as an `idLen(κ)`-bit identity, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 1 x s = S.sidImpl b κ pp msk 1 (cast x) s`. -/
theorem sidImpl_one_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 1 x s =
      S.sidImpl b κ pp msk 1
        (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s := rfl

/-- **Oracle `2` of the game, its query read as two messages**: the call on the game's query
type is the call on the query read as two `msgLen(κ)`-bit messages, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 2 x s = S.sidImpl b κ pp msk 2 (cast x) s`. -/
theorem sidImpl_two_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s := rfl

/-- **`KeyGen` for another identity, on the game's types**: with `ID*` recorded and the query
`x`, read as an identity, different from it, the answer is `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)`, read back on the game's answer type: for `cast x ≠ t`,
`S.sidImpl b κ pp msk 1 x (some t, c) =
(S.keyGen κ msk (cast x)).bind fun sk => pure (cast (decAnswer (some (encSK sk))), (some t, c))`. -/
theorem sidImpl_keyGen_ne_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
      Fin (S.idLen.eval κ) → Bool) ≠ t) :
    S.sidImpl b κ pp msk 1 x (some t, c) =
      (S.keyGen κ msk (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl)
        x)).bind fun sk =>
        .pure (cast (show (Fin (S.skLen.eval κ + 1) → Bool) = (S.sidSpec κ).rng 1 from rfl)
          (FixedLengthScheme.decAnswer (some (S.encSK κ sk))), (some t, c)) :=
  S.sidImpl_keyGen_ne b κ pp msk _ t c h

/-- **The first valid `Challenge`, on the game's types**: with `ID*` recorded, no challenge yet,
and both messages of the query `x`, read as two messages, in the message space, the answer is
`C ← Encrypt(params, ID*, M_b)`, read back on the game's answer type, and `C` is recorded: for
`(M₀, M₁) = splitHalf (cast x)` with `M₀, M₁ ∈ M`, `S.sidImpl b κ pp msk 2 x (some t, none) =
(S.enc κ pp t M_b).bind fun C => pure (cast (encCT C), (some t, some (encCT C)))`. -/
theorem sidImpl_challenge_fresh_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2) :
    S.sidImpl b κ pp msk 2 x (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2
        else (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1)).bind fun c =>
        .pure (cast (show (Fin (S.ctLen.eval κ) → Bool) = (S.sidSpec κ).rng 2 from rfl)
          (S.encCT κ c), (some t, some (S.encCT κ c))) :=
  S.sidImpl_challenge_fresh b κ pp msk _ t h
```

### 2.2 `IdentityBased/BonehBoyen.lean`: after line 412

Line 412 is `  exists_congr fun _ => List.ofFn_inj.symm`, the last line of `bb1Scheme_msgSpace_iff`.
- The block goes before the docstring of `bb1_correct`, after the `simps` attribute, whose lemmas
  its proofs use.
- It has 45 lines; source: `insertion/BonehBoyen-block.lean.txt`.

```lean
/-- **`Setup` at the scheme's types**: `Setup` runs the generator and BB1's `Setup`, and returns
`(⟨d, params⟩, ⟨d, (params, master-key)⟩)` as parameters and master key of `bb1Scheme G ℓ`:
`Setup κ = (sample r).bind fun r => (BB1.setup _).bind fun k => pure (⟨desc r, k.1⟩, ⟨desc r, k⟩)`,
the pair typed at `PP κ × MSK κ`. -/
theorem bb1Scheme_setup_eq (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) :
    (bb1Scheme G ℓ).setup κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
        .pure (((⟨G.desc κ r, k.1⟩ : (bb1Scheme G ℓ).PP κ),
          (⟨G.desc κ r, k⟩ : (bb1Scheme G ℓ).MSK κ)) :
            (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) := rfl

/-- **`KeyGen` at the scheme's types, followed by `f`**: for the master key `⟨d, (pp, mk)⟩` and an
`ℓ(κ)`-bit identity `ID`, `KeyGen` is BB1's `KeyGen` on `idToZ ID`, its key tagged with `d`:
`(KeyGen ⟨d, (pp, mk)⟩ ID).bind f = (BB1.keyGen pp mk (idToZ ID)).bind fun k => f ⟨d, k⟩`. -/
theorem bb1Scheme_keyGen_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (mk : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).SK κ → ProbComp β) :
    ((bb1Scheme G ℓ).keyGen κ ⟨d, (pp, mk)⟩ id).bind f =
      (BB1.keyGen pp mk (BB1.idToZ (G.group κ d) id)).bind fun k => f ⟨d, k⟩ := by
  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **`Encrypt` at the scheme's types, followed by `f`**: for the parameters `⟨d, pp⟩`, an
`ℓ(κ)`-bit identity `ID` and a `msgLen(κ)`-bit message `m`, `Encrypt` is BB1's `Encrypt` on
`idToZ ID` and `decodeT m` (the message read at the width of `G_T`), its ciphertext tagged
with `d`: `(Encrypt ⟨d, pp⟩ ID m).bind f = (BB1.encrypt pp (idToZ ID) (decodeT ⟦m⟧)).bind fun c =>
f ⟨d, c⟩`. -/
theorem bb1Scheme_enc_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).CT κ → ProbComp β) :
    ((bb1Scheme G ℓ).enc κ ⟨d, pp⟩ id m).bind f =
      (BB1.encrypt pp (BB1.idToZ (G.group κ d) id)
        (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))).bind fun c => f ⟨d, c⟩ := by
  rw [padFin_ofFn]
  simp only [bb1Scheme_enc, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **The ciphertext encoding as a word**: `⟦encCT ⟨d, c⟩⟧` is the padded word `A ‖ B ‖ C_1`
(`ctLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encCT (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (c : BB1.Ciphertext (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encCT κ ⟨d, c⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ) (List.ofFn ((G.group κ d).encT c.a) ++
        List.ofFn ((G.group κ d).encG c.b) ++ List.ofFn ((G.group κ d).encG c.c))) := rfl
```

## 3. Candidates dropped, and why

| Candidate | Status | Reason | Log |
|---|---|---|---|
| `IBEScheme.sidImpl_eq_oracleImpl` (whole function, Q7) | **dropped (fails)** | `rw` succeeds, but `oracleImpl_zero_onSpec` then finds no instance. Its handler `init := S.sidImpl b κ pp msk 0` has type `(S.sidSpec κ).dom 0 → …`, which is the handler type `(Fin (S.idLen.eval κ) → Bool) → …` only through `inLens`/`outLens`. The explicit instance is an application type mismatch | `alternatives/whole-fn/use-devsealA/` (3 errors; native rc 0) |
| its pointwise form `… i x s = S.oracleImpl … i x s` | **dropped (fails)** | the same | same log |
| `IBEScheme.sidImpl_one_onSpec` (Q7(B), answer cast back) | **dropped** | It serves no `KeyGen` case. The `⊥` answers `zeroBits (S.outLens κ 1)` cannot go through a cast from `Fin (skLen + 1) → Bool`. For `ID ≠ ID*`, `sidImpl_keyGen_ne`'s right side is a bind typed at `(Fin (skLen + 1) → Bool) × σ`, and `bind_assoc` cannot instantiate. Replaced by #3 and #5 | `alternatives/q7b-three-onSpec/devsealA-run/` (9 errors with Q7(B)'s three) |
| Q7(B)'s `sidImpl_two_onSpec` for all `Challenge` cases | **kept for the repeat case only** (#2) | The same failure for `⊥` (none, invalid) and for the fresh challenge. Hence #4 and #6 | same log |
| `bb1Scheme_keyGen_mk`, `bb1Scheme_enc_mk` (equation forms ending in `.pure ⟨d, k⟩`) | **dropped** | `.pure ⟨d, k⟩` puts a `Σ`-typed value at `SK κ`/`CT κ`, and `OracleComp.pure_bind` cannot instantiate on it under the seals. The bind forms #8 and #9 pass the value to the continuation, where the word readers apply | `alternatives/bb1-mk-readers/devsealA-run/` (2 errors) |
| no `encCT` reader: compare with `bb1SimCt` by `congrArg` (the brief's first choice) | **fails; `ofFn_bb1Scheme_encCT` (#10) kept** | `bb1SimCt_eq` reads `decodeT _ m` at the width `(bb1Scheme G ℓ).msgLen.eval κ` (its `G_T` is `BilinearGroup.GT _ (msgLen …) _`), `Encrypt` at `G.wT.eval κ`. The two agree only through `bb1Scheme`. With the word reader, both sides read `decodeT (padFin _ ⟦m⟧)` at `G.wT`, as T4's `ofFn_bb1SimCt` does, and #9 reads the message the same way | `alternatives/encCT-congrArg/use-devsealA/` (1 error; native rc 0) |
| the generated `simps` lemmas in place of #7–#9 | **fail** | `bb1Scheme_setup`'s right side is typed at `Σ … × Σ …`, so nothing composes after the rewrite. `bb1Scheme_keyGen`/`bb1Scheme_enc` bind the key and parameters at `Σ …`, the identity at `Fin (ℓ.eval κ) → Bool` and the message at `Fin (G.wT.eval κ) → Bool`, so they find no instance at the game's types | `alternatives/simps-lemmas/devsealA/` (8 errors) |
| nine per-case readers `sidImpl_*_onSpec` (one per typed reader) | **not proposed** | They would serve the same purpose with 9 readers instead of 6, each with a consumer-ready right side. Seyoon may prefer that uniform form | — |

Further development evidence: `scratch/explore2A`, `explore3A`, `explore4A` (anonymous
constructors, `Σ`-typed instantiation, the setup map).

## 4. P-2's algebraic hypotheses and their providers

Every hypothesis is an equation (or inequation) in `B.G`, `B.GT` or `ZMod B.order`, where
`B = G.group κ d`, `X = g^α` and `Y = g^{b'}`.
- None mentions an IBE definition.
- `bitsToNat` is `Asymptotic/Sampling`'s.
- The length `(bb1Scheme G ℓ).idLen.eval κ` in `hinj` is only an index.

| Lemma | Hypothesis | Content | Intended provider |
|---|---|---|---|
| `p2_init_none` | `e : Z_p → (G ≃ Z_p)`, `he : ∀ z h, h = X^{(−z).val} · g^{(e z h).val}` | for each `z`, `α₁ ↦ X^{−z} g^{α₁}` is a bijection `Z_p ≃ G` (design's `e : G ≃ Z_p` is its inverse) | deliverable-2 helper `BilinearGroup.pow_val_bijective_of_ne_one` (`{g : B.G} (hg : g ≠ 1) : Function.Bijective fun a : ZMod B.order => g ^ a.val`), through `Equiv.ofBijective`, composed with Mathlib's `Equiv.mulLeft`; the fill builds `e` |
| `p2_keyGen_ne` | `hinj : ∀ u v : Fin (idLen) → Bool, u ≠ v → (bitsToNat u : Z_p) ≠ bitsToNat v` | distinct identities stay distinct in `Z_p` (good coins, `2^ℓ ≤ p`) | deliverable-2 helper `BilinearGroup.natCast_inj_of_lt` (`{m n : ℕ} (hm : m < B.order) (hn : n < B.order) : (m : ZMod B.order) = n ↔ m = n`), with `bitsToNat_lt`, `bitsToNat_injective` and `2^ℓ ≤ p`; the fill |
| `p2_keyGen_ne` | `hkey : ∀ z z' a₁ r, z ≠ z' → Y^{α} (X^{z} (X^{−z'} g^{a₁}))^{r} = Y^{−a₁/(z−z')} (X^{z} (X^{−z'} g^{a₁}))^{r + b'/(z−z')} ∧ g^{r} = Y^{−1/(z−z')} g^{r + b'/(z−z')}` (exponents `.val`) | BB04's key identity: the real key with `r̃` is the simulated key with `r̃ + b'/(ID − ID*)` | deliverable-2 helpers `BilinearGroup.pow_val_add` (`x ^ (a + b).val = x ^ a.val * x ^ b.val`) and `pow_val_neg` (`x ^ (−a).val = (x ^ a.val)⁻¹`); published `pow_val_mul` (`Pairing/Group.lean`); Mathlib `pow_mul`, `mul_pow` and field arithmetic in `ZMod p` (`p` prime, `z − z' ≠ 0`); the fill |
| `p2_challenge_fresh` | `hF : ∀ z a₁, X^{z} (X^{−z} g^{a₁}) = g^{a₁}` | `F(ID*) = g^{α₁}` from `h = X^{−ID*} g^{α₁}` | deliverable-2 helpers `pow_val_add`, `pow_val_neg` (with `z + −z = 0`); Mathlib group lemmas |
| `p2_challenge_fresh` | `hT : ∀ s, e(X, Y)^{s.val} = e(g, g)^{(α b' s).val}` | the BDH value | published `BilinearGroup.bilinear_pow` and `pow_val_mul_GT` (`Pairing/Group.lean`); Mathlib `pow_mul` |

Proved inline from Mathlib's group API rather than taken as hypotheses:
- commutativity of `G_T` (`mul_comm`);
- `pow_right_comm` (`(g^{a₁})^{s} = (g^{s})^{a₁}`);
- `mul_assoc` with `mul_inv_cancel_left` (P-3).

## 5. Rows

**All rows are done; none is missing.** Every row holds natively and under devseal A and B.
- **P-1** (any `S : IBEScheme`, `x : (S.sidSpec κ).dom i`), nine lemmas: `p1_init_none`,
  `p1_init_some`, `p1_keyGen_none`, `p1_keyGen_target`, `p1_keyGen_ne`, `p1_challenge_none`,
  `p1_challenge_repeat`, `p1_challenge_fresh`, `p1_challenge_invalid`.
- **P-2** (`S = bb1Scheme G ℓ`):
  - the real side is `realAt` at the stored `h` (design's `bb1RealAt`), on states that carry `h`;
  - the simulator is `bb1SimImpl … g X Y`;
  - the relation is `RelM`, design §3.1's `R`.

  Sampling rows, in `expect_sample_rel`'s premise form:
  - `p2_init_none`: the real side draws `h`, the simulator draws `α₁`, along `e ID`;
  - `p2_keyGen_ne`: along `Equiv.addRight (b'/(ID − ID*))`;
  - `p2_challenge_fresh`: along `Equiv.refl`; the simulator side is the lazy
    `(sample Z_p).bind fun c => bb1SimImpl … (g^c) (e(g, g)^{αb'c}) 2 x _`.

  Deterministic rows, as equal `pure` answers with related states: `p2_init_some`,
  `p2_keyGen_none`, `p2_keyGen_target`, `p2_challenge_none`, `p2_challenge_repeat`,
  `p2_challenge_invalid`.

  Use site: `setup_out`.
- **P-3**: `p3_challenge_fresh` (`R := Eq`, along `Equiv.mulLeft (decodeT(M₁)⁻¹ · decodeT(M₀))`).
  It uses T4's readers only: `oracleImpl_two_onSpec`, `bb1SimChal_fresh`,
  `bb1Scheme_msgSpace_iff`, `ofFn_bb1SimCt`. **T3 needs no reader beyond T4's.**

## 6. Checks (`evidence/subagents/probe/`)

| Check | Result | Log |
|---|---|---|
| Readers probe `PlProbe/BB1SimReaders.lean` (174 lines, max width 100), native | rc 0, 0 errors (both forms), 0 warnings | `native-readers/` |
| Consumer `PlProbe/BB1SimStepM.lean` (586 lines, max width 100), native | rc 0, 0 errors, 0 warnings | `native-stepm/` |
| Consumer, devseal A (`PlProbe/Sealed/BB1SimStepM_A.lean`, 605 lines) | rc 0, 0 errors (both forms); `DEVSEAL A sealed 868` | `devseal-A/` |
| Consumer, devseal B (`…_B.lean`) | rc 0, 0 errors (both forms); `DEVSEAL B sealed 869` | `devseal-B/` |
| `#print axioms` (`PlProbe/BB1SimAxioms.lean`): 10 readers and 27 probe lemmas | 30 `[propext, Classical.choice, Quot.sound]`, 6 `[propext]`, 1 none; 0 non-standard | `axioms/summary.tsv` |
| No `sorry`, `admit`, `axiom`, `native_decide` or `@[simp]` in the three probe files | none (`grep`) | — |
| In-situ insertion (copies of both owners with the blocks) | rc 0, 0 errors; removal restores the bases | `insertion/` |

The development seals are T4's `devseal.py`, copied to `tools/devseal.py`. Its one change, a
harness line split for widths, is recorded in its header. These are not the canonical seals: those
run on the owners once the readers land.
