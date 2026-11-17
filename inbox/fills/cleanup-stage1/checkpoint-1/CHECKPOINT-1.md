# cleanup-stage1 · checkpoint 1: every target statement elaborates at the check tree

Worker: Claude in the cloud (lead plus two sub-agents, A and B). Date 2026-11-17 UTC. This checkpoint
carries checks 3, 11 and 12 of the brief (decls2, the StmtDump with the header check, the clash and
shadow scans, the reuse table), plus what was already done: the 847-module bootstrap, the first part of
the replay sweep (the import closure of every home), the axiom prints and the insertion check. **All
69 targets are proved (no `sorry`)**; the final adds the rest of the sweep, the Rule-10 seals (head and
base), controls, the explicit-unfold scan and the full report.

## Revisions

| | |
|---|---|
| Exchange pack | `d929cc21ec817b2518d57a7262e42744728f029a`, `shasum -a 256 -c SHA256SUMS`: 8/8 OK |
| Records (issue) | `f7308a62c3569c400051e8fe7e25663a94f8db8e` (`issued-r1/` byte-equal to the pack, 9 files) |
| Records tip at fetch | `8b5435eb31ffbca51218b2a72a381efd3a0c6141`: a descendant of `8adee3e6…` and `f7308a62…`; **no `.lean`, `lean-toolchain`, `lake-manifest.json` or lakefile change after `f99901fd…`** (it adds the seventh DL-35 approval, `ETTGame.dTape`, and the dispatch log: Stage 2 only) |
| Issue base | `daa6e173cdd94cad1475b9a96eca613bce53ba61` (`cleanup/dw5-derand-readers`, fetched by name) |
| Check base | `2081fe57475138297fff6a5144d31b91d7f27706` = issue base `--no-ff` merge of `f99901fdc98f4c7703cf9485329600311a1ea655`, tree **`01cc6259480ccc9372181cd4d18d4511c87aa048`** (as required); `SOURCE-SHA256SUMS` 847/847 OK |
| Branch `cleanup/stage1-promotions` (local) | head **`c8021348f9bc2d16cfa52ca5e8ff489dc9543592`**, 5 commits on the issue base, 21 files, +1,075 lines, 0 deletions |
| Check head | `caad0151d3bc3a29dfd23ed07dcc42ab16395cad` (check base `--no-ff` merge of the branch), tree **`985dd3125d8fd588cf2c8faa31ced8dee88407ab`** = `git merge-tree --write-tree f99901fd… c8021348…` (**equal**) |

`patches/` holds `git format-patch daa6e173…..c8021348…` and `COMMITS.tsv` (signing `none` for all
five). `git am --committer-date-is-author-date` of the series at the issue base, in a scratch clone with
committer `Claude <noreply@anthropic.com>`, reproduces all five hashes.

## Environment (addendum Part 1)

Preflight (`build/preflight.log`): 4 CPUs; cgroup v1 limit 14,338,760,704 B, in use
(usage − total_cache + total_shmem) 38,490,112 B, **headroom 13.32 GiB**; clone filesystem ext4,
**26.12 GiB free**. Toolchain `leanprover/lean4:v4.25.0` via elan (installed after the preflight). Cache
store `~/.cache/mathlib` absent before the fetch (`cache-store.log`). Narrowed fetch: the **164** Mathlib
roots imported by `order.txt` (`mathlib-roots.txt`; the issued `roots.txt` has 166 lines, the other two
being core `Std.Sat.CNF` and the word `the` from a docstring line `import the counter loop.` of
`Complexity/TuringMachine/Build/Contract/Counter.lean:19`): "Attempting to download 3246 file(s)",
3,246 decompressed, exit 0 (`cache-get.log`); 0 empty oleans; package check: 11 present match the
manifest, 4 ABSENT (doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean; none imported); probe `import
Mathlib.Algebra.BigOperators.Field` rc 0.

## Builds so far (one Lean process at a time, host-wide `flock`, `scripts/lean_check_tree.sh`)

- **Bootstrap** of `order.txt` at the check base: **847/847 rc 0, 0 errors** in both forms, every source
  bound to `git show HEAD` (tree `01cc6259…`); `sorry` warnings **26 in 12 modules = `base-sorries.txt`
  module by module**; 5,455 s of module time, max RSS 3.6 GiB (`build/bootstrap-results.jsonl`). The
  runner was stopped once after module 150 (to add a lock yield for the sub-agents) and resumed from
  151; module 151 had finished unrecorded and was rechecked (`build/bootstrap-NOTES.txt`).
- **Sweep, part 1** at the check head: the 129 modules of the sweep (changed modules and their
  downstream) that lie in the import closure of the 19 homes and the two facades, in `order.txt` order
  with `Games/Tapes` after 477 and `ZeroKnowledge/InteractionWords` after 558: **129/129 rc 0, 0 errors**
  (`build/sweep-part1-progress.txt`). Part 2 (the other 366 of the 495) is running.

## Check 3: statements

- **decls2** (`statements/decls2.tsv`; the records' `decls2.py` at `fa81981a…`, branch head against the
  issue base, over the 21 new and changed files): **ADDED 69 = exactly the targets, CHANGED 0,
  REMOVED 0.**
- **StmtDump** (`statements/StmtDump.lean.txt`, `StmtDump.log`): rc 0, prints all **69** constants
  (`STMT-COUNT 69`) with full name, kind, `protected` flag and type; kinds (7 `def`, 62 `theorem`) and
  `protected` (54) equal the brief's table.
- **Header check** (`statements/headercheck.txt`, `tools/headercheck.py`): the brief's text of every
  target against the head source, both normalized by decls2's own parser: **69/69 equal.** No
  statement change.
- **Axioms** (`statements/Axioms.log`): all 69 within {`propext`, `Classical.choice`, `Quot.sound`}
  (34 all three, 12 `propext`+`Quot.sound`, 6 `propext`, 4 `Classical.choice`, 13 none); **no
  `sorryAx`**.

## Check 11: name clash and shadow (`checks/clash/`)

(a) Exact full-name clashes with any declaration (public or private) in `TCSlib/` or `audits/` at the
check base: **0**. (b) Every target whose short name exists elsewhere is `protected`: **54 protected,
0 unprotected with an existing short name, 0 mismatches with the brief's `P` marks**
(`shortname.tsv` lists each same-short-name hit; they are the Stage 2 copies and homonyms).
(c) Shadow scan over the 495 sweep modules: **361 unqualified occurrences, 0 needing attention**: 53
are the new declarations' own lines; the rest are uses in modules inside or opening the new name's
namespace (mostly `ETTGame`'s `ovr`/`tapeImpl`/`freshImpl` in the ETT files, which open
`TCSlib.Cryptography.Games` and keep resolving to `ETTGame.*` because every `Games` form is
`protected`); fresh names had no declaration to resolve to. The sweep's elaboration of these modules
(part 1 already, part 2 running) is the mechanical confirmation.

## Check 12: reuse (`reuse/reuse-table.md`)

Name, shape and Mathlib/core greps for every target and 23 `exact?` calls at the check base: **no
E-DUP.** Every copy line of the brief is confirmed at the check tree. Further copies for the Stage 2
table: S1-11 `Authentication/Signatures/Lamport/MachineSpec.lean:259`,
`Authentication/Signatures/HashAndSign/CollisionHandler.lean:464`; S1-15
`SecureComputation/Yao/HybridProof/RowFromCoins.lean:416`; S1-16 `Asymptotic/CollectionsHelpers.lean:112`,
`Hashing/FromDiscreteLog.lean:97`, `:134`, `Asymptotic/Collections.lean:796`, `:804`;
S1-23 near-copies `Encoding/DyadicUniform.lean:83`, `:148`, `:216`.

## Other checks already run (final repeats them)

- **Insertion check** (`checks/insertion/`): 19 changed files, 41 declared anchors (the Scope table's),
  **PASS**: every change is an insertion at its anchor, and removing the blocks restores each issue-base
  file byte for byte (base SHA-256s equal the Scope table's); controls (character changed, line deleted,
  extra line, block moved) give the stated result on all 19 files (**ALL_OK**).
- Lint, sizes, docstrings and sketches (pre-run, final will carry the logs): no new `style_lint`
  finding; campaign lint at base/head Cryptography 92/104 → 92/103 (one WARN removed: `pkPredictor`
  now has its reader), InformationTheory 5/2 → 5/2, Complexity 25/390 → 25/390, no new FAIL or WARN
  line; every added line ≤ 100 characters, largest file `Asymptotic/Sampling.lean` 965 lines,
  `ZeroKnowledge/EncodingMachines.lean` 867; all 69 docstrings state the formula and carry the tag or
  glue note, every proof of ≥ 15 lines has a sketch.

## Who wrote what

Lead: S1-04 (`Games/Tapes.lean`), S1-05, S1-08, S1-10, S1-12, the `Games.lean` facade; integration,
commits, checks. Sub-agent A: S1-06, S1-07, S1-09, S1-11, S1-15, S1-18 to S1-22, S1-26, S1-27, the
`ZeroKnowledge.lean` facade. Sub-agent B: S1-01 to S1-03, S1-14, S1-16, S1-17, S1-23 to S1-25. Each
sub-agent worked in its own worktree and olean tree, checked through the shared lock, and handed its
files back as a patch, which applies at the issue base and equals its worktree byte for byte.

## Questions for Seyoon (recommended option first)

- **CS1-W1 (`EncodingMachines.zeros_poly`, S1-27).** The reuse search found two public, inter-derivable
  forms the brief does not list: `Games.EffFill.zeros_poly` (`Games/Efficiency/Strings.lean:152`) and
  `EnsembleLemmas.polyTimeComputable_zeros` (`Asymptotic/EnsemblesLemmas.lean:212`). Neither is in
  `EncodingMachines`' import closure, and neither has the unary-length hypothesis that `padTo_poly`
  uses. (a) **Keep `zeros_poly` as the brief states it** (done), with the overlap disclosed and the two
  older forms left for a later dedup; (b) drop it and inline the zero word in `padTo_poly` (68
  declarations; the ThreeColoring copy `ThreeColoring/Machines.lean:292` would then have no Stage 2
  target).

## Notes (no ruling needed)

- S1-14: `TCSlib.Cryptography.encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean:60`) already has the
  equal statement in public; the brief lists it as the Stage 2 copy, so the promotion is as intended.
- The `ZeroKnowledge.lean` `## Contents` entry is the brief's text in the facade's backtick style:
  ``* `InteractionWords` — the history encoding as a word list (`BinArith.encWords`).``
- `InteractionWords.lean` has a `## Main definitions` section reading "None; this module proves one bridge
  lemma." (the policy header; `style_lint` asks for it).
