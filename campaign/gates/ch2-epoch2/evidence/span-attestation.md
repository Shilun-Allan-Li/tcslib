# Maintainer whole-epoch attestation — Chapter 2, epoch 2

Evidence for the epoch-2 audit pack (`audits/ch2-epoch2-pack.md`). Every
claim below was produced by the maintainer from the repository alone,
independent of the delivery agents' own attestations. Span:
`f317f0c7` (close of the epoch-1 gate) → `2e176f60` (B2 integration
attestation); the pack commit follows.

## 1. Commit enumeration

**Ten Codex-authored fill commits, nine zip deliveries** (replayed
byte-identically from `git format-patch` series before each `git am -3`;
per-delivery verification recorded in the `AroraBarakChapter2Plan.md`
decision log at each integration):

| Zip | Commit(s) | File(s) | REPORT |
|---|---|---|---|
| fill-ch2-e2-A | `da8bd091` | EXP.lean | batchA.md |
| fill-ch2-e2-B | `3e076219` | Nondeterminism.lean | batchB.md |
| fill-ch2-e2-C | `53a884cd` | NP.lean, Reductions.lean | batchC.md (+ batchC-continuation.md, its filed continuation plan) |
| fill-ch2-e2-D | `4b4cd418` | TMSAT.lean | batchD.md |
| fill-ch2-e2cont-A | `7fa3c08d` | EXP.lean | batchA-cont.md |
| fill-ch2-e2cont-B | `42e2f65f`, `4df03129` | Nondeterminism.lean | batchB-cont.md |
| fill-ch2-e2cont-C | `db617dea` | NP.lean | batchC-cont.md |
| fill-ch2-e2cont-D | `9f748601` | TMSAT.lean | batchD-cont.md |
| fill-ch2-e2cont-B2 | `1514fd6b` | Nondeterminism.lean | batchB2.md |

**Three maintainer integration commits** (`a6c1804a`, `e72d95bf`,
`2e176f60`): verified by `git show --stat` to touch **no `.lean` source**
— records, logs, programs, and reports only.

**Interleaved, separately audited material.** The entire
machine-construction-library campaign sits inside this git span
(`71d90d39` design freeze → `64d82f84` fill-gate close) and was audited
under its own two gates (`audits/ch1-infra-resolutions.md`,
`audits/ch1-libfill-resolutions.md`). One of its commits, `e8dd3e57`
(bridge export), is the only non-Codex commit in the span that touches an
epoch-2 file: its `TMSAT.lean` slice (the discharge of the sanctioned
bridge `timed_universal_quantitative`, 1,185 → 1,206 lines) was
byte-decomposed and proof-audited at the infra gate (that pack's scope
item and freeze item 4). It is therefore **out of scope** for the epoch-2
gate.

No other commit in the span touches the five owned files. Per-file
`git log f317f0c7..HEAD -- <file>` outputs are exactly the rows above
(plus `e8dd3e57` for TMSAT.lean).

## 2. Per-file ledger (baseline `f317f0c7` → HEAD)

| File | Lines | Public decls | Private decls | New imports (whole span) |
|---|---|---|---|---|
| EXP.lean | 143 → 2,887 | 6 → 6 | 0 → 135 | `Build.Primitives` |
| Nondeterminism.lean | 239 → 2,627 | 8 → 8 | 0 → 110 | `Simulation`, `Build.Primitives`, `Mathlib.Tactic.FinCases` |
| NP.lean | 137 → 679 | 3 → 3 | 0 → 38 | `Build.Primitives` |
| Reductions.lean | 210 → 477 | 10 → 10 | 0 → 16 | none |
| TMSAT.lean | 244 → 1,908 | 5 → 6 | 0 → 87 | `Build.Primitives`, `Universal` (bridge, audited), `Mathlib.Tactic.Ring`, `Mathlib.Tactic.DeriveFintype` |

All imports are order-legal in the committed 57-module list (the owned
files sit after `Build/` and `Universal`); no cycles.

**Public-surface freeze.** Name-level extraction
(`^(theorem|lemma|def|abbrev|instance|structure|inductive|noncomputable
def) <ident>`) at baseline vs HEAD is **identical for every file except
TMSAT.lean, which adds exactly `timed_universal_quantitative`** — the
bridge statement sanctioned in advance by batch 2D's bridge protocol,
added by the 2D checkpoint, and statement-and-proof audited at the infra
gate. Three flush-left docstring prose lines beginning with a declaration
keyword (`EXP.lean:457` "lemma proves …", `TMSAT.lean:698` "lemma from
Chapter 1 …", `TMSAT.lean:703` "theorem with the private startup …")
are grep artifacts, inside `/- … -/` blocks, not declarations.

**Net deletion audit (whole span).** The net diff of the five files
deletes exactly:

- **11 `sorry` lines** — the eleven closed theorem names (EXP 1,
  Nondeterminism 3, NP 1, Reductions 2, TMSAT 4);
- **6 docstring tail lines** (EXP 1, Nondeterminism 2, TMSAT 3) — each
  the closing line of a sketch docstring re-emitted with an append-only
  completion note (per-delivery deleted-line audits confirmed
  append-only at each integration);
- **1 statement line** (`NP.lean`, `mem_NP_iff_exists_length_le`'s
  `∃ u : List Bool, …` line) — the 2C checkpoint's recorded cosmetic:
  re-emitted token-identical with a doubled space before `:= by`
  (disclosed and verified at checkpoint integration).

Nothing else is deleted in-span. Intermediate placeholders (the
checkpoints' `CONTINUATION` markers, the checkpoint-admitted private
`enumMachine_contracts`, the 2B frontier comment) were added and removed
inside the span, so they cancel in the net record.

## 3. Private-helper arithmetic

Per-REPORT new-private counts, cross-checked against the per-file
`^private ` counts at HEAD:

| Stratum | A | B | C | D | Σ |
|---|---|---|---|---|---|
| Checkpoints | 40 | 32 | 34 | 41 | 147 |
| Continuations | 95 | 36 | 20 | 46 | 197 |
| B2 | — | 42 | — | — | 42 |
| **Σ** | **135** | **110** | **54** | **87** | **386** |

HEAD per-file counts: EXP 135, Nondeterminism 110, NP 38 + Reductions 16
= 54 (batch C owned both), TMSAT 87. **Total 386 = 147 + 197 + 42
exactly**; the bridge-export commit added zero privates to TMSAT.lean.

## 4. Admission ledger

Fresh-olean sweeps over the committed module order at each integration
(all logs under `audits/logs/`):

| State | Commit | Modules | Admissions |
|---|---|---|---|
| Baseline (epoch-1 gate closed) | `f317f0c7` | 53 | 32 |
| Checkpoints integrated | `a6c1804a` | 53 | 29 (= 32 − 5 target bodies written + 2 new sites: `enumMachine_contracts`, the bridge) |
| Continuations integrated | `e72d95bf` | 57 | 23 (= 2 B frontiers + 5 padding + `EXP_subset_NEXP` + 15 E3/E4) |
| B2 integrated | `1514fd6b` | 57 | **21** (= 5 padding + `EXP_subset_NEXP` + 15 E3/E4) |

Final distribution (from `ch2-e2cont-B2-integration-sweep.log`):
Nondeterminism 5 (epoch-3 padding), EXP 1 (`EXP_subset_NEXP`), SAT 3,
Tautology 2, CookLevin 10. Net over the span: −11 = the eleven closed
names. 32 − 11 = 21.

## 5. Closure attestation

Maintainer kernel type/value traversal (opaque values and constructors
included), program committed at `audits/programs/ch2-e2-ClosureAxioms.lean`,
run against the fresh sweep oleans at `1514fd6b`
(`audits/logs/ch2-e2cont-B2-axioms.log`, exit 0): all twelve closure
names (the eleven targets plus the bridge) have **empty admission-root
sets and at most the standard triple**; the Chapter-1 headline and
library regressions (`timed_universal`, `timed_universal_concrete`,
`exists_loopCfgTM`, `computesFunInTime_splitSolve`, `capture_run`)
unchanged; `EXP_subset_NEXP` at exactly its own root.

Earlier integration traversals (`ch2-e2-checkpoint-axioms.log`,
`ch2-e2cont-axioms.log`) confirmed every intermediate `sorryAx` root
exactly as disclosed at each stage, including the A/C-cluster funnel
through the single admitted private `enumMachine_contracts`.

## 6. Policy

Lint at `2e176f60` (`audits/logs/ch2-e2cont-B2-lint.log`), ClassNP
scope: **0 FAIL, 3 WARN** — the recorded size exceptions EXP 2,887,
Nondeterminism 2,627, TMSAT 1,908 (each justified at its integration
under exclusive single-file fill ownership; extraction/dedup is the
recorded E5/D7 follow-up). Repo-wide, the only FAILs are 14 pre-existing
items in `NPReductions/*`, untouched by the span (no span commit touches
that directory).
