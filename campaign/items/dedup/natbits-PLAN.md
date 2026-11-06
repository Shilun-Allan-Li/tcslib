# NatBits dedup plan (BL-1 + NB-1, with LS-3 and BL-2's lemma)

Plan only, nothing edited. Tree: `complexity/arora-barak-ch3-4`. The Lean tree is the same at
`7cdcc9ba` and `c942799e`, the HEAD when this was written; the commits in between touch only the
ledger and the gate records. Line numbers are at that tree.
Import-graph counts come from parsing every `import TCSlib.*` line (925 modules, without the
`TCSlib` root).

## 0. Findings that shape the plan

- `Machines/Bin` imports **Mathlib only** (`Data.Nat.Size`, `Data.Nat.Log`, `Tactic.Ring`). No cycle
  stops any file from importing it. "Cannot reach `Bin`" in the ledger is about the layering rule (a
  `TuringMachine/`, `ClassNP/`, `CookLevin/` or `Diagonalization/` file importing
  `SpaceComplexity/Machines`), not about a cycle. NatBits removes that problem.
- **Every member file already reaches `Encoding`.** So once `Encoding` imports NatBits, no site
  needs a new `import` line.
- E-D (#188) has merged. `qy_call_bound` (iii) already cites `Turing.length_bits_le_self` (`NTimeDiagonalizer:456`).
  `Complexity.Codec.two_pow_bits_le` no longer exists: #181 moved it to `Bin`.
- The open PRs into the campaign branch are #208, #211, #212, #213, #214 and #215. Only **#208**
  (`lean/ch34-deepen-landing`) touches our files:
  - `Bin`: it adds `LogProg.length_bits_succ_le` between `length_bits_le` and `two_pow_bits_le`, a
    **textual conflict with the move**;
  - `Mult`, at :534;
  - `SpaceAmplifyPoly`, at :111.

  The last two hunks are disjoint from our sites.
- The parked `lean/dedup-ro1` (no PR) touches `Encoding`, `NTimeDiagonalizer`, `Catalog`,
  `CfgRecord` and `ExhaustiveReplay`:
  - in `Encoding`, an import-block line at :9, which is adjacent to our import edit;
  - in the other four files, hunks disjoint from our sites.
- **Sequencing:** land after #208 merges, so that `length_bits_succ_le` moves too and no
  NatBits change conflicts with `Bin`.

## 1. Canonical statements hosted in `TCSlib/Complexity/TuringMachine/NatBits.lean`

These are moved verbatim and keep their full names, so nothing downstream is renamed:

| Kind | Statement | Canonical (today's home) | Other public statements |
|---|---|---|---|
| (i) | `n < 2^m → \|bits n\| ≤ m` | `Complexity.LogProg.length_bits_le` (`Bin:124`) | none |
| BL-2 | `m ≤ 2^e+1 → \|bits (m+1)\| ≤ e+2` | `Complexity.LogProg.length_bits_succ_le` (`Bin`, on #208) | none |
| (ii) | `a ≤ b → \|bits a\| ≤ \|bits b\|` | `Complexity.LogProg.length_bits_mono` (`Bin:142`) | none |
| (iii) | `\|bits m\| ≤ m` | `Turing.length_bits_le_self` (`Encoding:290`) | none |
| (v) | `1 ≤ L → 2^\|bits L\| ≤ 2L` | `Complexity.LogProg.two_pow_bits_le` (`Bin:132`) | `Randomized.PolyAmp.two_pow_bits_le` (`SpaceAmplifyPoly:243`), the 2n+1 form, which already cites it |
| LS-2 converse (NB-1) | `\|bits n\| ≤ log₂ n + 1` | `Complexity.LogProg.length_bits_le_log` (`Bin:146`) | none |

These are moved or added, with new full names:

| Kind | Statement | Proposed name | Source |
|---|---|---|---|
| (iv) | `n < 2^\|bits n\|` | `Complexity.LogProg.lt_two_pow_bits` | moved from `Randomized.PolyAmp.lt_two_pow_bits` (`SpaceAmplifyPoly:249`); only the namespace changes. Its two users, `:260` and `:280`, resolve through `open Complexity.LogProg` with no edit, and it has no other users. |
| (iv) on `posWidth` | `n+1 < 2^posWidth n` | `Turing.record_pos_lt` **stays** in `CfgRecord:242` | It reads `posWidth`, a definition in that file. It is re-proved as `lt_two_pow_bits (n+1)`. |
| (v), 2n+1 form (NB-1) | `2^\|bits n\| ≤ 2n+1` | new: `Complexity.LogProg.two_pow_bits_le_two_mul_add_one` | replaces `PolyAmp.two_pow_bits_le` and `qy_two_pow_bits_le` (D2b) |
| LS-3 (NB-1) | `n ≠ 0 → \|bits n\| = log₂ n + 1` | new: `Complexity.LogProg.length_bits_eq_log` | LS-3's ruled disposition: "beside `length_bits_le_log`" |
| (vi), `ofDigits` form | `ofDigits 2 (w.map toNat) < 2^\|w\|` | new: `Complexity.LogProg.ofDigits_lt_two_pow` | only if D4 is accepted |

(vi), `bitsVal` form: **stays** in `Bin` as `Complexity.LogProg.bitsVal_lt_two_pow` (`Bin:87`), the
canonical form. Moving it would bring the `bitsVal` definition and its four companion lemmas down into
the TuringMachine layer (D4). Its exact copy `Complexity.Codec.bitsVal_lt_two_pow` (`Codec/Word:463`) is
deleted (D2c).

Optional move into NatBits, with names kept: `Turing.bits_two_pow_mul` and
`Turing.bits_two_pow_eq_replicate` (`Encoding:303`, `:314`; 8 references), the `Nat.bits` shift law.
They are not ledger members (D6).

### Name clashes and namespaces

- **NatBits has two namespace roots**, `Turing` and `Complexity.LogProg`, because the full names are
  kept. This deviates from policy §1's "one root per topic" (D1). A single root would rename either
  `Turing.length_bits_le_self` (52 references in 21 files) or the four `LogProg` names (77 references in
  about 40 files).
- `PolyAmp.lt_two_pow_bits` would clash, as an ambiguous overload, with the new
  `LogProg.lt_two_pow_bits` inside `SpaceAmplifyPoly`, which has `open Complexity.LogProg`. So the move
  must delete it in the same commit.
- `PolyAmp.two_pow_bits_le` has the same short name as `LogProg.two_pow_bits_le`, with a different
  statement. It compiles today because the current namespace takes priority. Deleting it makes its one
  user, `:273`, cite the new 2n+1 name.
- A grep for each moved name finds no other declaration that could become visible to modules that reach
  `Encoding` but not `Bin`.
- Files in `namespace Turing…`, such as `RecordTable`, `InputLength`, `Catalog`, `CfgRecord` and
  `NTimeDiagonalizer`, cite `Complexity.LogProg.<name>` in full. No `open` is needed.

### File conventions

NatBits follows policy §1 and §2:
- the header: copyright with authors Seyoon Ragavan and Hydroxyi (the authors of the moved lemmas), the
  three standard options, and `# Title`, `## Main results` and `## References` ([AB09], as `Bin` and
  `Encoding` do);
- docstrings that begin with the statement (the moved ones are kept);
- a `Contents` line in `TCSlib/Complexity/TuringMachine.lean`. `TCSlib.lean` already imports that
  facade.

The file is about 130 lines.

## 2. Imports, and why there is no cycle

| Module | Imports today | Imports after the move |
|---|---|---|
| `TuringMachine/NatBits` (new) | none | `Mathlib.Data.Nat.Size` and `Mathlib.Data.Nat.Log`, plus `Mathlib.Data.Nat.Digits.Defs` if D4 is accepted. **No TCSlib import.** |
| `TuringMachine/Encoding` | `Mathlib.Data.Fintype.EquivFin`, `Mathlib.Data.List.FinRange`, `Mathlib.Data.Nat.Bits`, `Mathlib.Data.Nat.Size`, `TuringMachine.StateRenaming`, `TuringMachine.Robustness.SingleTape` | Adds `TuringMachine.NatBits`. `Mathlib.Data.Nat.Size` can be dropped: only `:291–292` use it. |
| `SpaceComplexity/Machines/Bin` | `Mathlib.Data.Nat.Size`, `Mathlib.Data.Nat.Log`, `Mathlib.Tactic.Ring` | `TuringMachine.NatBits`, `Mathlib.Data.Nat.Log` (still used by `succ_le_two_pow_log` and `log_poly_bound`), `Mathlib.Tactic.Ring` |

There is no cycle, by construction: NatBits imports no TCSlib module, and `Encoding` and `Bin` both
import it.

The new edge from `Bin` to `TuringMachine/` goes in the normal direction, from `SpaceComplexity` down to
`TuringMachine`.

Check at implementation: `length_bits_le_log`'s `by norm_num` needs `Nat.one_lt_two`, or
`Mathlib.Tactic.NormNum.Basic`. `Bin` got `norm_num` through `Tactic.Ring`.

## 3. Member sites to re-point

Columns:
- "Today": whether the site's file reaches the target lemma without NatBits.
- "Import": every file listed reaches `Encoding`, so after PR A none needs an import edit.

| # | Site | Kind | Today's closing | Re-point to | Today | Owner | Branch overlap |
|---|---|---|---|---|---|---|---|
| 1 | `Diagonalization/NTimeDiagonalizer:416–424` `qy_ones_ge` | (iv) ×2 | `size_eq_bits_len` ×2 and `Nat.lt_size_self` ×2 | `lt_two_pow_bits n`, `lt_two_pow_bits D` | no | E-D's (landed) | dedup-ro1: disjoint hunks |
| 2 | same file, `:427–440` `qy_two_pow_bits_le` | (v) 2n+1, with LS-3 inline (`hsz`) | `Nat.size_le` both ways | delete. Users `:3638`, `:4388`, `:4506`, `:7690` and docstrings `:4382`, `:4433`, `:7686` cite the 2n+1 lemma | no | same | same |
| 3 | same file, `:443–450` `qy_log_bits` | LS-3 | `Nat.size_le` both ways | delete. Users `:3780` and `:4453` use `(length_bits_eq_log _).symm` | no | same | same |
| 4 | same file, `:3252–3255` `qy_bits_len_mono` | (ii) | `Nat.size_le_size` | delete. Users `:3630` and `:8302` (docstring `:8266`) use `length_bits_mono` | no | same | same |
| 5 | same file, `:3258–3260` `qy_lt_two_pow_bits` | (iv) | `Nat.lt_size_self` | delete. Users `:3602` and `:3635` use `lt_two_pow_bits` | no | same | same |
| 6 | same file, `:7678–7684` `dz_word_lt` | (vi) `ofDigits` | Mathlib's `ofDigits_lt_base_pow_length` | delete. User `:7689` uses `ofDigits_lt_two_pow` (D4) | no | same | same |
| 7 | `Build/RecordTable:2761–2762` | (ii) | `simpa [size_eq_bits_len] using Nat.size_le_size` | `Complexity.LogProg.length_bits_mono (Nat.le_succ _)` | no | campaign's | none |
| 8 | `Build/InputLength:417–418` and `:419–420` | (ii) ×2 | same | `length_bits_mono` ×2 | no | campaign's | none |
| 9 | `Build/Catalog:4124–4125` | (ii), size form | `rw [..., size_eq_bits_len] at hcarry`, `Nat.size_le_size hi` | drop the rewrite; `length_bits_mono hi` | no | campaign's | dedup-ro1: disjoint |
| 10 | `Build/CfgRecord:242–245` `Turing.record_pos_lt` (public, kept) | (iv) | `unfold posWidth`, `size_eq_bits_len`, `lt_size_self` | `unfold posWidth` (own file); `lt_two_pow_bits _` | no | campaign's | dedup-ro1: disjoint |
| 11 | `CookLevin/Hardness:1130–1146` `clCount_width`; `:2255–2256` `clElapsed_width` | (i) by binary induction; (iii) through (i) | `Nat.binaryRec'` | delete `clCount_width` (its only user is `:2256`). `clElapsed_width` becomes `(Turing.length_bits_le_self n).trans hn` | **yes** (`Encoding`) | campaign's | none |
| 12 | `Logspace/Mult:254`, `:255` (`mult_product_length`) | (iv) ×2 | `simpa [size_eq_bits_len] using Nat.lt_size_self` | `lt_two_pow_bits a` and `lt_two_pow_bits b` (`open LogProg` at `:51`) | no | campaign's | **#208** (hunk at `:534`, disjoint) |
| 13 | `Logspace/QueryReshape:192–205` `query_index_bound` | (v), native | `Nat.size_le`, `lt_size`, `size_pos` | `r < 2^\|bits r\| ≤ 2^\|bits n\| ≤ 2n` by `lt_two_pow_bits`, `pow_le_pow_right` and `LogProg.two_pow_bits_le` (case `n = 0` apart) | (v) yes; (iv) no | campaign's | none |
| 14 | `Randomized/UniformSample:93–101` `Randomized.le_two_pow_size_pred` (public, kept) | (v) positive branch, native | `Nat.lt_size`, `pow_succ'` | second conjunct by `← size_eq_bits_len` and `two_pow_bits_le (N-1)` (case `N = 1` apart) | **yes** (`Bin`) | Hydroxyi's | none |
| 15 | `Codec/Word:462–468` `Complexity.Codec.bitsVal_lt_two_pow` (public) | (vi), exact copy | induction | delete. Users `Word:473`, `Deciders:141`, `Layout:218`, `Layout2:168`, `Parse:88`, `StepDecider:346`, `:375` resolve to `LogProg`'s through `open Turing LogProg`, which all six files have | **yes** (`Bin`) | Hydroxyi's | none |
| 16 | `Randomized/QuasiPolyHierarchy:58–64` `length_bits_eq` | LS-3 (`if`-form) | `Nat.size_le` and `lt_size` | delete. User `:211` splits on `n = 0` and cites `length_bits_eq_log` | no | Hydroxyi's | none |
| 17 | `SpaceComplexity/Constructible:76–83` `b3a_bits_length` | LS-3 (through `logSpace`) | `Nat.lt_size`, `length_bits_le_log`, `unfold logSpace` | `(length_bits_eq_log hn).trans (logSpace_eq n).symm`. This also drops an `unfold logSpace` of another file's definition. | no | campaign's | none |
| 18 | `ClassNP/ExhaustiveReplay:1807–1810` `xr_val_lt` | (vi) `ofDigits` (a promotion request, not a ledgered member) | Mathlib | `ofDigits_lt_two_pow` through `xr_val`, its own file's definition | no | campaign's | dedup-ro1: disjoint |
| 19 | `Randomized/SpaceAmplifyPoly:273` (`bigK_le`) | consequence of D2b | `PolyAmp.two_pow_bits_le` | the 2n+1 lemma | — | Hydroxyi's | **#208** (hunk at `:111`, disjoint) |
| X1 | `CircuitComplexity/Meyer:188–189` (`lenAll_inst`) | (i) | `size_eq_bits_len`, `Nat.size_le.mpr` | `Complexity.LogProg.length_bits_le hjW` | no | **colleague-owned: excluded** | none |
| X2 | `CircuitComplexity/MeyerTableau:436–437` (`bits_pad`) | (i) | same | `length_bits_le hj` | no | **excluded** | none |

**Counts:**
- 19 non-colleague declarations in 13 files: rows 1–18, plus row 19's consequential edit. Row 18 is
  conditional.
- 2 colleague-owned sites.
- Three are re-pointable today, without NatBits: rows 11, 14 and 15.

### Searched and classified non-members

The search covered `size_eq_bits_len`, `Nat.size_le`, `Nat.lt_size(_self)`, `Nat.size_le_size`,
`Nat.size_pos`, `binaryRec'`, `lt_two_pow_self` next to `bits`, every `have …bits….length ≤/<`, and
`… < 2 ^ ….length`. Nothing found is a re-derivation of the kinds above:
- **Citations:**
  - `PrimeFind:204`, `:317`, `:470–474`; `CodeSimulator:1446`; `RecordTable:4253`;
    `Constructible:441–444`; `NARMExample:96`;
  - `RandomWalkPad:154`; `BPLInP:402`; `PathHard:90`, `:94`; `ISCountGenCorrect:217–218`;
  - every `two_pow_bits_le`, `length_bits_mono` or `length_bits_le_log` user.
- **Native `Nat.size` facts:**
  - `Jacobi` and `ModPow` (`size_lt_of_two_mul_le`);
  - `ISCountMath:67` `lt_two_pow_size_succ`;
  - `RandomWalkPad:149`;
  - `UniformSample:95` (the first conjunct is Mathlib's `lt_size_self`) and `:264`;
  - `Catalog:4166`; `Programs/Light/Lib/Emod`.
- **LS-family steps:**
  - `PathHard:82` (`logSpace_le_ell`, a stronger bound);
  - `BPLInP:396–398` and `:438–440`, and `SpaceAmplifyPoly:254`: LS-2 converted to the bits form.

## 4. PR split and replay closure

The replay closure counts the changed modules plus every module downstream of them, out of 925.

| PR | Changes | Changed files | Replay closure |
|---|---|---|---|
| **A**: create NatBits and move the publics | new `TuringMachine/NatBits`; `Encoding` (delete `:289–292`, plus `:294–316` if D6, import, docstring `:75–77`); `Bin` (delete `:123–147` and `length_bits_succ_le`, import, docstring `:33–36`); `SpaceAmplifyPoly` (delete `:242–250`, re-point `:273`); the `TuringMachine.lean` facade (import, `Contents`) | 4 existing + 1 new | **340** (`Encoding` 324 ∪ `Bin` 189, plus `SpaceAmplifyPoly` and the facade) |
| **B**: re-point the sites | rows 1–18: `NTimeDiagonalizer`, `RecordTable`, `InputLength`, `Catalog`, `CfgRecord`, `Hardness`, `ExhaustiveReplay`, `Mult`, `QueryReshape`, `UniformSample`, `Codec/Word`, `QuasiPolyHierarchy`, `Constructible` | 13 | **143** (130 downstream); every module in it is also in A's 340 |
| **A + B** in one PR | — | 17 + 1 new | **340**: B adds no module to A's closure |
| **C** (needs authorization): `CircuitComplexity` | `Meyer`, `MeyerTableau` (no import change) | 2 | **13** |

B's closure by file:
- `Catalog` 114, `InputLength` 73, `Constructible` 69, `CfgRecord` 68, `RecordTable` 67, `Word` 61;
- `Hardness` 25, `QueryReshape` 17;
- the rest 1–3 each.

**Recommendation:** land A and B as one PR, since B adds no module to the replay. Split them only if
review size matters (one PR has 18 files).

**Variant (D5):** keep `Turing.length_bits_le_self` in `Encoding`, and leave `Encoding` unchanged. NatBits
is then imported directly by the 6 site files that do not reach `Bin` (`RecordTable`, `InputLength`,
`Catalog`, `CfgRecord`, `NTimeDiagonalizer`, `ExhaustiveReplay`). The closure is then **237** instead of 340,
but NatBits is no longer below `Encoding`, against the ruling's wording.

**Census effect:**
- `Bin`'s "5/15" one-fifth review item goes away: four of its five canonical statements move to
  NatBits, the canonical home, and `bitsVal_lt_two_pow` stays.
- `NTimeDiagonalizer` loses 6 members. `Hardness` 2 → 0, `QueryReshape` 1 → 0, `UniformSample` 1 → 0,
  `Word` 1 → 0.

## 5. Decisions for the user

- **D1 (namespaces):** NatBits carries two namespace roots, `Turing` and `Complexity.LogProg`, so that
  no downstream name changes. This is a policy §1 deviation, noted in the module docstring.
  - The alternative is one root, with renames: 52 references in 21 files, or 77 in about 40.
  - Recommend: keep both roots.
- **D2 (public removals and renames):**
  - **(a)** `Randomized.PolyAmp.lt_two_pow_bits` becomes `Complexity.LogProg.lt_two_pow_bits`. It is
    deleted from `SpaceAmplifyPoly`; it has no external users.
  - **(b)** `Randomized.PolyAmp.two_pow_bits_le` (the 2n+1 form): delete it, in favour of the new
    `Complexity.LogProg.two_pow_bits_le_two_mul_add_one` (one user, `:273`). The alternative is to keep
    it, as a second public statement of the 2n+1 form beside NatBits'.
  - **(c)** Delete `Complexity.Codec.bitsVal_lt_two_pow` (an exact copy; its 7 uses resolve to `Bin`'s).
- **D3 (new names):** `length_bits_eq_log` (LS-3, hypothesis `n ≠ 0`, orientation `|bits n| = …`),
  `lt_two_pow_bits`, and `two_pow_bits_le_two_mul_add_one`. Confirm the names, and confirm that LS-3 is
  paid in this PR.
- **D4 ((vi) home):** keep `bitsVal_lt_two_pow` (with `bitsVal`) in `Bin`. Host an `ofDigits`-form
  `Complexity.LogProg.ofDigits_lt_two_pow` in NatBits for `dz_word_lt` and `xr_val_lt`. Or leave those
  two on Mathlib's `Nat.ofDigits_lt_base_pow_length`, which each re-derives in 3 lines. Also: is
  `xr_val_lt`, a promotion request, in scope?
- **D5:** move `Turing.length_bits_le_self`, as the ruling says (closure 340), or keep it in `Encoding`
  (closure 237).
- **D6:** also move `length_bits_succ_le` (recommended: one home; needs #208 merged) and the optional
  `Turing.bits_two_pow_mul` / `bits_two_pow_eq_replicate`.
- **D7:** PR C for the colleague-owned `Meyer:188–189` and `MeyerTableau:436–437`.
- **D8 (blueprint):** `blueprint/src/chapter/Complexity/TuringMachine/Encoding.tex:528` binds
  `Turing.length_bits_le_self`. The name is unchanged, so the binding still holds. Should the entry move
  to a NatBits chapter? Run `blueprint_validate --strict` either way.
- **D9 (scope widenings found, none acted on):**
  - **Positivity** `0 < |bits n|` from `Nat.size_pos`, with no public lemma: `RecordTable:192–194`,
    `:4685–4687`, `:5909–5910`, `InputAccess:995–997` and `ISCountMath:63` (the round-5 sweep classed
    these "other").
  - **Halving width**: `Complexity.LogProg.ISCount.size_half` (`ISCountMath:60`, size form) and
    `Complexity.LogProg.access_width_half` (`InputAccess:993`, bits form) are two publics of one fact.
    `UPathWalk:116`'s private `size_eq_succ` is a third copy of `size_half`.
  - **One width, three definitions**: `Turing.posWidth` (`CfgRecord:211`), `Complexity.Codec.wP`
    (`Word:280`) and `Complexity.PathHard.ell` (`PathHard:65`) all define `|bits (n+1)|`.
  - **(vi) over other value functions**: `EXP:127` `enumValue_lt` (private); `MeyerTab:68` `ctrVal_lt`,
    `LupanovGates:132` `ofBits_lt` and `HardFunctions:106` (all `CircuitComplexity`). This is
    value-function unification; `Bin:45` already flags `BoolCircuit.bitsVal`.
