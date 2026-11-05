# External audit pack: four configuration facts, one public home each (PR #190, an API gate)

## Why this PR

The maintainer reviewed NF cont1's delivery, the linear normal form `exists_codeNDTM_accepts_linear`
in `ClassNP/NDNormalForm`. The review, `campaign/fills/c1/reviews/nf-cont1-fill/REVIEW.md`, found in
its F2 four private lemmas that re-state facts other files already state privately (or, for the
fourth, publicly in a file NF cannot import). By kind:
- **(i)** the input read depends on the input head only;
- **(ii)** a live configuration redirected to `⟨i, q⟩` is phase `i`'s tagged configuration;
- **(iii)** a configuration tagged by phase `i` is at no state of another phase;
- **(iv)** a list of equal-length chunks has length count × chunk length.

The user ruled on 2026-11-04: **publish homes first**. This PR gives each fact one public home and
re-points the private copies in the campaign's files. NF's landing will then cite the four lemmas.
The ledger entry is "NF cont1's delivery, F2" in `campaign/duplication-ledger.md`.

**The PR:** #190 on `lean/cfg-facts`, head `3cc6c9ee4837f03a27446c4a64e17078b9b63876`
(`evidence/patches/`). Its commits:
- `74ef5df2`, the change;
- a merge of the campaign after #184;
- `95d54ce2`, which renames the chunk-length lemma (see question 5);
- `8c0a85c7`, which adds the module docstring's References section (campaign lint's one FAIL);
- `d198d907`, which publishes the general fact behind (ii), `Cfg.mapState_eq_of_fields` (see
  question 4);
- `f76e3eac` and `3cc6c9ee`: `ExhaustiveReplay`'s `xr_phase_step` (two blocks) and `xr_halt_fixed`
  (two blocks) convert renamed configurations through it. At `d198d907` the screen paired them
  with it at 93% and 78%.

## What changed (verify)

| File | Change |
|---|---|
| `TuringMachine/CfgFacts` (new) | (i) `Turing.Cfg.inputSymbol_congr`; (ii) `Turing.Cfg.mapState_const_eq_mapState_sigma`, derived from the general `Turing.Cfg.mapState_eq_of_fields` (a renamed configuration is any configuration with its data fields and the renamed state); (iii) `Turing.Cfg.mapState_sigma_state_ne`; (iv) `Turing.length_flatMap_uniform`. It imports only `StateRenaming` |
| `ClassNP/ExhaustiveReplay` | the private `xr_inputSymbol_congr` is removed, and its one use cites (i); `xr_phase_step` and `xr_halt_fixed` cite `Cfg.mapState_eq_of_fields` for their four field-by-field conversions |
| `TuringMachine/Build/ZoneRebalance` | the private `zr_inputSymbol_congr` is removed; its one use cites (i) (`Cfg.inputSymbol_congr _ _ rfl`), and its docstring mention is updated |
| `TuringMachine/Build/CfgRecord` | the private `record_tag_ne` is removed, and its use cites (iii); the private `recordStep_mapState_eq` is removed, and its three uses cite `Cfg.mapState_eq_of_fields` |
| `TuringMachine/Build/SeamLayout` | the privates `sl_rewrap` and `sl_tagged_ne_done` keep their statements (seven call sites each), and their bodies now cite (ii) and (iii) |
| `TuringMachine.lean` | imports `CfgFacts`; its line in the module list |

## Brief for the auditor

1. **The statements.** Is each stated in its natural generality? Is each faithful to the copies it
   replaces?
   - (i) holds across machines with different tape counts and state types;
   - (ii) takes `c.state.isSome` where `sl_rewrap` took `c.state = some st₀`;
   - (iii) is `record_tag_ne` made public.
2. **The proofs** read other files' definitions only through published equations (rule 10):
   - `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end` and `inputSymbolInner` for
     `Cfg.inputSymbol`;
   - the `Cfg.mapState_*` equations of `StateRenaming`;
   - `List.length_flatMap`, `List.map_const'` and `List.sum_replicate` (core), with the core
     reduction `n • c = n * c` by `rfl`.

   **The seal** (`evidence/rule10/`): a sealed copy of `CfgFacts`, with `Cfg.inputSymbol` and
   `Cfg.mapState` irreducible and the usual `simp` erasures, elaborates with 0 errors. Controls:
   4 of 4 pass unsealed, and 0 of 4 pass sealed. The re-pointed sites cite and unfold nothing new.
3. **The re-points:** are they faithful, and statement-preserving for `sl_rewrap` and
   `sl_tagged_ne_done`?
4. **Duplication** (`evidence/screen/`): the v3 screen of 10 files at the head against the campaign
   tip `057da7a7`: 953 declarations on both sides, 745 → 740 pairs, 3 new and 8 gone
   (`pairdiff-cf.txt`). The new pairs are `CfgFacts`' retag lemma against
   `Cfg.mapState_eq_of_fields`, which it cites (74%, in-file), and two RN-1 members,
   `SeamLayout.exists_seamLayoutTM` (67%) and `ZoneRebalance.zr_short_fields` (61%). The gone pairs
   are those of the removed private copies. The ten files are the five changed ones and the files
   with the copies:
   - `Configuration`, `StateRenaming` and `Seam`;
   - NF's `NDNormalForm`, whose four copies remain until its landing;
   - `CircuitComplexity/PSubsetPPolyTableau`, with the public
     `Complexity.CfgTableau.length_flatMap_const`.

   The remaining inline field-by-field conversions of renamed configurations, the content of
   `Cfg.mapState_eq_of_fields`, form the family **RN-1, acknowledged by the user by kind**
   (2026-11-04) for the dedup window (12.2c). Under TEMPLATE failure mode 5 a further member is an
   accounting minor. Among them are `SeamLayout.exists_seamLayoutTM`, `ZoneRebalance.zr_short_fields`
   and NF's 15 inline retag steps.
   So is the `CircuitComplexity` lemma, which needs its own authorization because the file is
   colleague-owned. Is anything else re-derived?
5. **Names** (`evidence/names/`): no ref declares the new names. The chunk lemma was first named
   `length_flatMap_const`, and it is renamed because `Complexity.CfgTableau.length_flatMap_const`
   exists in four `CircuitComplexity` files that open both `Turing` and `CfgTableau`.
6. **Lint** (`evidence/lint/`).

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): the new file and the four changed files compiled with
  `lean -o`, in dependency order, into a copy-on-write clone of `oleans-larm2`, all with no output.
  After each later commit the changed files were recompiled into the same clone, again with no
  output: `CfgFacts`, `CfgRecord`, `SeamLayout` and `ExhaustiveReplay`; `ZoneRebalance` is
  unchanged since the chain.
- **Axioms** (`evidence/axioms/`): all five lemmas within `[propext, Classical.choice, Quot.sound]`;
  `mapState_sigma_state_ne` uses none, and `mapState_eq_of_fields` only `Quot.sound`.
- **Replay:** `replay-lcf2` (`evidence/merged-tree/`), the six files' downstream closure,
  83 modules, chained from `oleans-ledge`, at `95d54ce2`. **It passed:** 83 of 83, static-equal.
  The head adds `Cfg.mapState_eq_of_fields`, `CfgRecord`'s and `ExhaustiveReplay`'s re-points and
  the docstring. #190's closure overlaps #189's, and #190 is to merge second.
  Its certifying replay is therefore the merged-tree replay of the head on the campaign after
  #189, which covers the docstring commit.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/94-cfg-facts-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `cfg-facts-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
