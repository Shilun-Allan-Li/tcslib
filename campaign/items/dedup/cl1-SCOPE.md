# CL-1 scope: the codec languages' sibling idiom

Worktree `/home/user/tcslib-scratch/wt-cl1`, branch `lean/dedup-cl1` at `origin/complexity/arora-barak-ch3-4`
(`f4dfc3f3`). Line numbers are at that base. Paths are relative to `TCSlib/Complexity/`.

**Status: stopped after scope.** The brief's stop rule applies: two deviations from the ledger's
disposition are needed (questions Q1 and Q2 at the end). No Lean file has been edited.

## 1. Members

Closing forms:
- **D3** (decode, triple, at `bits c`): `rintro ⟨x', c', s', h, hC⟩`, then `pairEncode_inj` twice,
  `rw [bits_injective h3, bits_injective h4]`, `exact`; reverse direction `⟨x, c, s, rfl, h⟩`.
- **D3w** (decode, triple, at a word `w`): `rintro ⟨x', c, s', h, …⟩` through the set-builder, then
  `pairEncode_inj` twice (`rfl`, `rfl`), `obtain rfl := bits_injective h4`, `cfgWord_eq_bits_iff`;
  reverse direction `⟨x, cfgCode s C, s, by rw [bits_cfgCode], …⟩`.
- **D4 / D4w**: the same for the quadruple `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`, with `pairEncode_inj`
  three times.
- **W1** (decider wrapper): the `arm_decides_poly (CA N mode) .lenScan codecAs codecAs_mem
  (8 * W N + 8) 1` preamble, `rw [← val_empty]`, `AHalt.mono … gd_mono`, the `one_run` case split,
  the accepting branch (`indicator_eq_of_iff`, `hsh.1`, `X_iff`, `validChk_iff_pre`, `hst`), and the
  reject branch (decode the member, `shape_of_code`, `X_iff.mp`, `validChk_iff_pre`, `hfail`).
- **R10**: the proof reads a `Codec/Langs` definition in another file by definitional unfolding
  (`rintro`/`obtain` through the set-builder, or an anonymous constructor that builds a member).
  Rule 10 forbids this.

| # | Declaration | File:line | Closing form | Reads the language through |
|---|---|---|---|---|
| 1 | `mem_validLang` | `SpaceComplexity/Codec/Langs.lean:117-126` | D3 | home file (allowed) |
| 2 | `mem_initLang` | `Langs.lean:129-138` | D3 | home file |
| 3 | `mem_acceptLang` | `Langs.lean:141-151` | D3 | home file |
| 4 | `mem_stepLang` | `Langs.lean:154-167` | D4 | home file |
| 5 | `mem_edgeLang` | `Langs.lean:172-183` | D3, after `rw [mem_edgeLang_iff]` | `mem_edgeLang_iff` |
| 6 | `validLang_iff` | `SpaceComplexity/Codec/Checks.lean:388-398` | D3w | **R10** (`rintro`, :392; constructor, :398) |
| 7 | `initLang_iff` | `Checks.lean:402-412` | D3w (init form) | **R10** (:406, :412) |
| 8 | `acceptLang_iff` | `Checks.lean:416-426` | D3w | **R10** (:420, :426) |
| 9 | `stepLang_iff` | `Checks.lean:430-444` | D4w | **R10** (:435, :443) |
| 10 | `edgeLang_iff` | `Checks.lean:512-522` | D3w, after `rw [mem_edgeLang_iff]` | `mem_edgeLang_iff` |
| 11 | `validLang_mem` | `SpaceComplexity/Codec/Deciders.lean:198-220` | W1, tail = `AHalt.ret` | **R10** (reject branch :215 `obtain`, :217 constructor) |
| 12 | `acceptLang_mem` | `Deciders.lean:226-248` | W1, tail = `AHalt.ret` | **R10** (:243, :245) |
| 13 | `initLang_mem` | `Deciders.lean:385-416` | W1, tail = `init_tail`, plus the `hyl`/`hs` lines (:392-394) | **R10** (:411, :413) |
| 14 | `edgeLang_mem` | `Deciders.lean:760-788` | W1, tail = `edge_tail`, plus `rw [← orc_eq]` and the same `hyl`/`hs` lines (:768-770) | `mem_edgeLang_iff` (:783) |

The shared pieces already in place are kept: `pairEncode_inj` (`Langs:110`), `mem_edgeLang_iff`
(`Langs:103`), `cfgWord_eq_bits_iff` (`Checks:380`), and in `Deciders` the lemmas
`indicator_eq_of_iff` (:179), `shape_of_code` (:185), `gd_mono` (:72), `val_empty` (:77),
`validChk_iff_pre` (:95) and `one_run` (:107).

The census matches the ledger: `Langs` has 5 membership lemmas (plus the 5 definitions, which stay),
`Checks` has 5 `_iff` lemmas, and `Deciders` has 4 deciders.

## 2. Same closing form, not members (skipped)

| Site | File:line | Why it is skipped |
|---|---|---|
| `stepLang_mem` | `SpaceComplexity/Codec/StepDecider.lean:297-423` | It is not in the ledger's census (`Deciders` 3/16 → 4/22 only). Its run is `parse_run₂`, `layout_run`, `layout2_run`, `insym_run`, `vscan_run` and `step_tail`, with no `one_run` split, so a one-code wrapper does not fit it. It shares only the 3-line preamble and the reject helper `hnon` (:304-312, which is also **R10**: :309, :312). |
| `one_run`'s `huniq` | `Deciders.lean:130-135` | Uniqueness of the `Shape1` decomposition: `pairEncode_inj` twice, then `bits_injective`, word against word. This is not a language membership, so the membership lemma does not serve it. |
| `stepLang_mem`'s `huniq` | `StepDecider.lean:324-330` | The same, for `Shape2` (`pairEncode_inj` three times). |
| `parse_run`, `parse_run₂` | `SpaceComplexity/Codec/Parse.lean:289-292, 325-332, 369, 411-413, 454-458` | `pairEncode_inj` on a shape, then `pairDecode`/`canon`. A different closing; no `bits_injective`. |
| `reflTransGen_stepRel` | `ClassPSPACE/TQBFHardMachine.lean:116-122` | Decodes a `stepLang` member at a word (`obtain … := id hst`, then `pairEncode_inj` three times and `bits_injective` twice). This is **R10** in Seyoon's file, outside `SpaceComplexity` and outside the five languages' declarations. Once Q1 is settled, it is a natural consumer of the shared lemma. |
| `mem_iff_mid` | `TQBFHardMachine.lean:192-199` | Decodes `initLang` and `acceptLang` members at words (D3w twice). **R10**; same remark. |
| `PathHard`, `PathHardDecide` | `SpaceComplexity/Logspace/PathHard.lean:244-251`, `PathHardDecide.lean:174` | Other encodings (`pathRaw`, `qLang`), not the code triple. |

All other consumers of the five languages read them through `mem_initLang`, `mem_acceptLang`,
`mem_stepLang`, `mem_edgeLang`, the `_iff` lemmas or `_mem`: `Bridge`, `SavitchARM/*`, `ExpBFS/*`,
`Logspace/ISCountGen*`, `PathHard*`, `Randomized/SpaceAmplifyPoly*` and `TQBFHardVerifier`. None of
them changes.

## 3. Proposed statements

### 3a. The shared membership lemma (`Codec/Langs`, after `pairEncode_inj`)

```lean
/-- **Membership in a language of encoded triples.** Let `L` be a language whose members are
exactly the encodings `⟨x, ⟨bits c, enc t⟩⟩` with `P x c t`, for an injective encoding `enc` of
the tail. Then, for every word `w`, `⟨x, ⟨w, enc t⟩⟩ ∈ L` exactly when `w` is the binary word of
some `c` with `P x c t`. The code languages are of this shape: tail `bits s` for `validLang`,
`initLang`, `acceptLang` and `edgeLang`, and tail `⟨w', bits s⟩` for `stepLang`.

Configuration-graph infrastructure ([AB09, §4.1.1]); not a result of [AB09].

**Proof sketch.** A member `⟨x', ⟨bits c, enc t'⟩⟩` equal to `⟨x, ⟨w, enc t⟩⟩` has `x' = x` and
`bits c = w` by injectivity of the pairing, in both layers, and `t' = t` by injectivity of `enc`.
Conversely, `⟨x, ⟨bits c, enc t⟩⟩` is a member when `P x c t` holds. -/
theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
    {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
      y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
    (x w : List Bool) (t : τ) :
    pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t
```

The re-proofs would be:
- `mem_X` for the four triple languages: `(mem_codeLang_iff bits_injective hL x (bits c) s)`, then
  `simp only [bits_injective.eq_iff, exists_eq_left]`.
- `mem_stepLang`: the same with `τ := List Bool × ℕ`, `enc t := pairEncode t.1 (bits t.2)`, and
  `P x c t := ∃ c', bits c' = t.1 ∧ …`. Here `hL` is a three-line reshuffle of `stepLang`'s
  `∃ x c c' s`.
- `X_iff` in `Checks`: `rw [chkIff, mem_codeLang_iff bits_injective hL]`, then the word/code
  conversion through `bits_cfgCode` and `cfgWord_eq_bits_iff`. That conversion could go in one
  private helper in `Checks`, for the `∃ C, InWindow ∧ cfgCode = c ∧ R C` shape.

### 3b. The decider wrapper (`Codec/Deciders`, after `shape_of_code`)

```lean
/-- **The decider wrapper of the one-code modes.** Let `L` be a language of encoded triples
`⟨x, ⟨bits c, bits s⟩⟩` with `P x c s`, where `P x c s` makes `c` the code of some configuration.
Let `Chk` be a word-level check that is membership at `⟨x, ⟨w, bits s⟩⟩` and implies the validity
test. Suppose that, in the one-code mode `mode`, the tail of the codec machine after the
validity scan answers `Chk x s w` from the registers `one_run` leaves, on every well-shaped
input that passes the pre-scan checks. Then `L` is in `L` (logspace).

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a result of
[AB09] by itself.

**Proof sketch.** Apply `arm_decides_poly` with the codec machine in mode `mode` and the register
bound `bnd`. In the common run (`one_run`), either the machine reaches the end of the scan, where
the tail answers the check, which is membership; or it rejects, and then no decomposition of the
input passes the pre-scan checks. In that case the input is not a member: a member is well
shaped (`shape_of_code`) and passes the check, hence the validity test and so the pre-scan checks
(`validChk_iff_pre`). -/
theorem oneCode_mem (hm : mode ≠ .step) {L : Language Bool} {P : List Bool → ℕ → ℕ → Prop}
    {Chk : List Bool → ℕ → List Bool → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧ P x c s)
    (hP : ∀ x c s, P x c s → ∃ C : Cfg N.k Bool N.State x, cfgCode s C = c)
    (hchk : ∀ x w s, pairEncode x (pairEncode w (Nat.bits s)) ∈ L ↔ Chk x s w)
    (hval : ∀ x s w, Chk x s w → ValidChk (N := N) x.length s w)
    (htail : ∀ (y x w : List Bool) (s : ℕ) (st : VAd N) (R : Regs), Shape1 y x w s →
      PreChk N x.length s w → s ≤ 2 * y.length → W N * (2 * s + 1) ≤ w.length →
      st.1 = vScan N (w.take (W N * (2 * s + 1))) → R.Bd (bnd N y) →
      R.A = 2 * x.length + 2 → R.S = s → R.T = 0 →
      R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) →
      ∃ b : Bool, (b = true ↔ Chk x s w) ∧
        AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
          (some (.vDone st), R.val, none) b) :
    L ∈ LOGSPACE
```

`htail` is the mode's tail. It returns the existing `AHalt.ret …` for `valid` and `accept`,
`init_tail …` for `init` and `edge_tail …` for `edge`, each with its existing `hind` conversion
(the check against the tail's verdict) as the `b = true ↔ Chk` part. The wrapper takes over the
`hyl`/`hs` lines that `initLang_mem` and `edgeLang_mem` repeat, and the `rw [← orc_eq]`.
`stepLang_mem` stays as it is (§2).

Neither statement adds an import: `Langs` already has `pairEncode`, `bits` and `bits_injective`, and
`Deciders` has everything 3b names. No existing statement or name changes.

## 4. Questions for the user (why I stopped)

**Q1 (blocking): rule 10 needs four more public declarations.** The `_iff` lemmas of `Checks`
(rows 6-9) and the deciders of `Deciders` (rows 11-13) can only use 3a/3b if they can read
`validLang`, `initLang`, `acceptLang` and `stepLang` as sets of encoded tuples. That is the `hL`
hypothesis. Both directions need it:
- the `→` direction of `X_iff` has to rule out a word `w` that is no `bits c`;
- the reject branch has to decompose a member.

`mem_X` (at `bits c`) cannot supply it. Today these files read the definitions by `rintro`, which is
the R10 column. Only `edgeLang` has a published characterization (`mem_edgeLang_iff := Iff.rfl`,
`Langs:103`, the precedent cited by gate 96 F1). A Rule-10-clean re-proof therefore needs, beside
`mem_edgeLang_iff`:
`mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`, `mem_stepLang_iff`
(each `y ∈ X N ↔ <the set-builder body>`, `Iff.rfl`, with a docstring stating the formula). These are
four public declarations beyond the disposition's two, on Hydroxyi's interface. `policy.md` §1
allows them ("definitions that predate the rule … are covered as consumers need them"). Options:
- **(a)** Add the four (recommended). All 14 members are then re-proved and the R10 reads in rows
  6-9 and 11-13 disappear.
- **(b)** Re-point only what is clean without them: rows 1-5, 10 and 14. Leave rows 6-9 and 11-13 at
  their base text, about two thirds of the family.
- **(c)** Re-prove rows 6-9 and 11-13 with `hL := fun _ => Iff.rfl` in `Checks`/`Deciders`. This
  breaks rule 10 in new text, so I would not do it without an explicit waiver.

**Q2: `stepLang` is a quadruple.** The disposition names "one membership lemma for languages of
encoded triples". `stepLang` is `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`, and `stepLang_iff` is at two
words `w`, `w'`. My proposal (3a) keeps one lemma by making the tail generic: an injective `enc`,
with tail `⟨w', bits s⟩` for `stepLang`. The cost is a three-line `hL` reshuffle for `stepLang`.
The alternative is a second, quadruple lemma. Please confirm the generic-tail reading. Also confirm
that `stepLang_mem` stays out of the wrapper, as the census implies: its run has no `one_run` split.

**Q3 (not blocking, for later): sites outside CL-1.** Two items:
- `TQBFHardMachine`'s `reflTransGen_stepRel` and `mem_iff_mid` (Seyoon's file) decode the same tuples
  by R10 reads; with (a) they could be re-pointed to 3a.
- The `Shape1`/`Shape2` uniqueness decodes in `one_run`/`stepLang_mem` repeat the same
  `pairEncode_inj`/`bits_injective` chain on words, which a decoding lemma would serve.

Both are outside the disposition, and I would not touch them in this PR.

## 5. Environment

- The worktree is created and clean; `.lake/packages` is symlinked.
- No olean overlay was made, so there is nothing to remove.
- When I stopped, the replay `oleans-lcamp2` was about 35 of 195 modules in, with no
  `# modules=195 failed=0` line yet.
