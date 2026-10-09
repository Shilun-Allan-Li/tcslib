# External audit pack — Chapter 4, phase P4.3, round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P4.3, round 2. Round 1 (`audits/ch4-p43-findings.md`, attached verbatim)
returned **1 blocker, 4 majors, 4 minors, 3 notes**; per `workflow.md` §3 the
gate did not close. This round audits the repairs. The gate closes on zero
blockers and zero majors.

Audited at commit `aa02db41` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch4-p43-r2-repairs.diff`, the range `200f4693..aa02db41`
restricted to the three repaired files): **one statement changed**
(`exists_adjacency_codec_cnf`, the blocker), **one definition added**
(`Turing.Cfg.InWindow`), and six proof sketches plus the module docstring's
deviations bullet rewritten. Every other declaration of the phase is
byte-identical to the round-1 surface, checkable in the diff.

**Layering update since round 1**: the P4.2 gate is now **CLOSED** (round 1,
PASS — `audits/ch4-p42-resolutions.md`, attached). The restated codec
deliberately factors through that closed surface's vertex quotient
(`Turing.NDTM.coreSum`, the three-valued `Turing.OutSummary`), exactly the
repair direction round 1 proposed; round-1 note 10's cross-filing is
disposed there (no P4.2 defect found). The P4.4 gate also closed; §12
remains under concurrent audit, cited by fill-engine references only.

## Brief for the auditor

You have the round-1 report. For each finding, the table below states the
repair and where it lives; the complete change is the attached diff. Your
deliverables:

1. For **finding 1 (the blocker)**: audit the restated
   `Complexity.exists_adjacency_codec_cnf` as a fresh statement — blind-restate
   it, then check it against your own round-1 repair guidance: the codec's
   injectivity now reaches only the input and the vertex quotient
   (`x = x'` across inputs; `coreSum c = coreSum d` within one input); the
   windowed side condition is the new `Turing.Cfg.InWindow`; the adjacency
   equivalence reads `coreSum (M.tm.step c) = coreSum d`; validity (`φv`)
   characterizes exactly the codec image among length-matching strings;
   acceptance (`φacc`) is halted state plus `accept` summary; cross-input
   pairs are rejected by `φa`; and all three CNFs carry `numVars` and
   **serialized-length** bounds. Is the restatement true, and is it strong
   enough for the hardness route of your round-1 answer 5?
2. For **each major and minor (2-9)**: verify the repair matches your
   proposed fix or say why the deviation is inadequate. Majors 4 and 5
   repaired the *sketches* only — confirm the statements never needed to
   change.
3. Report anything the repairs broke or newly misstate — in particular,
   check the new `Cfg.InWindow` definition and the restated package's
   quantifier structure for fresh defects — in the same findings-table
   format and severity scale as round 1.

Sources as in round 1 ([AB09] §4.2, §4.1.3, Exercise 3.2).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `ClassPSPACE/TQBF.lean` (the restated codec package, `Turing.Cfg.InWindow`, the rewritten deviations bullet, the membership and hardness sketches), `ClassPSPACE/Games.lean` (the `determined` sketch), `SpaceComplexity/Hierarchy.lean` (the `space_universal` and `space_hierarchy` sketches, the padding clause of `SPACE_linear_ne_NP`, one docstring bullet) |
| Unchanged, re-attached for context | `Formulas/{QBF,QBFEncoding}.lean`, both facades, and every statement of the three repaired files other than the codec package (byte-identity checkable in the diff) |
| Declared, out of scope | the same commit range also contains: the P4.2/P4.4 gate closures (their findings, resolutions, and seven swept docstring minors in `ConfigGraph`/`Logspace/*` — closed gates, attached as context), the phase-P3.3 statement skeleton (`TuringMachine/NDCodes.lean`, `Diagonalization/NTimeHierarchy.lean` — its own future gate), and plan/backlog bookkeeping. Also out of scope: tactic proofs; round-1 notes 11-12 (dispositions below) |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **blocker** — fixed-length injective codes on full configurations are impossible (unbounded output; pigeonhole at `n = s = 0`) | Restated over the quotient carrier, per your guidance: `code` is injective **down to `(x, coreSum)`** on `Cfg.InWindow`-windowed configurations; the output enters only through the summary; adjacency compares `coreSum (step c)` with `coreSum d`. Your `c_j` family now has equal codes *required* (all `j ≥ 2` are `dead`-summary with equal cores), and the halted self-loop reads `coreSum (step c) = coreSum c` — consistent, no pigeonhole |
| 2 | **major** — the existential package supplies no uniform construction | The package now declares itself **existence, not an algorithm** (docstring bullet + hardness sketch): the uniform polynomial-time emitter of `φv`/`φa`/`φacc`, the initial-vertex code, and the level scaffolding are **private, named fill obligations of `TQBF_PSPACEHard`** — your proposed option (b) |
| 3 | **major** — unguarded midpoints invent paths through junk codes | The package now carries `φv` with an exact image characterization (both directions, over all length-matching strings) and cross-input rejection; the hardness sketch's recursion guards the midpoint with `Valid` and quantifies an `Accept` target — your `Valid`/`Next`/`Accept` interface |
| 4 | **major** — `space_universal` sketch: window-membership is not a cell count; streamed output cannot be retracted | Sketch rewritten (statement unchanged, as you noted it could be): visited-interval **cardinality** via min/max counters checked including the final configuration (`s = 0` always fails; your `0 → 1` instance counts two cells); the core-count clock with the periodicity argument; **probe silently, then replay** for the output contract; the canonizer cost a finite code-dependent constant, no `O(length α)` claim |
| 5 | **major** — `space_hierarchy` sketch: `∀ α, ∃ Cα` gives no uniform `O(g)` bound | Sketch rewritten (statement unchanged) to your increasing-budget repair: budgets `s = 0, …, g n` over fixed banks, the fixed universal's own heads **hard-capped** in `[-g n, g n]` (uniform in `α`), first-success flip with a three-valued attempt summary, one **fixed code with padded payload**, the **space-preserving one-work-tape normal form named as a fill obligation** (a time-only normal form is not a space ledger), domination at `A := C_α·(c₀ + 2)` through the bundled floors; `f`'s constructibility contributes only its floor |
| 6 | minor — `ψ₀ = adjacency` misses zero-length paths at live vertices | The hardness sketch's base is now `Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` |
| 7 | minor — the codec's listed tracks omitted the scanned input | The codec now carries the **input-content track** (plus the one-hot position track), keeping the formulas input-independent; `φa` conjoins content-track equality and reads the scanned bit under the position marker |
| 8 | minor — the literal-occurrence sum misses empty clauses | All three size clauses now bound `(CNF.serialize ·).length` directly (plus `numVars`); the sketch cites the serialization-length equation with clause count explicit |
| 9 | minor — mover-relative game value flips polarity | `determined`'s sketch now fixes the **player-one perspective** (`V h` = player one can force `W = true`; OR at even, AND at odd histories) and extracts both strategies by polarity |
| 10 | note — [P4.2] carrier distinction | Filed to the P4.2 round, which closed with no defect; disposition in `audits/ch4-p42-resolutions.md` (its note 6 carries the bridge obligations) |
| 11 | note — junk-code attribution under the abstract scheme | No change: the abstract `code` makes no per-string attribution, and `space_universal` never needs one; recorded |
| 12 | note — attestation posture | This round attaches the repair diff itself; revision identity and olean freshness remain maintainer attestations, stated to verify or challenge |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p43-r2-sweep.log`, revision recorded at
  start: `aa02db41`): all seven modules, both facades listed, 0 `error:`
  lines, fresh `.olean`s, exactly **12** `declaration uses 'sorry'` warnings
  (QBF 1, QBFEncoding 1, TQBF 5, Games 1, Hierarchy 4; facades 0) — the
  inventory is unchanged by the repairs (one statement restated in place,
  one definition added).
* Style lint (`audits/logs/ch4-p43-r2-stylelint.log`): `Formulas` 0 FAIL /
  0 WARN over 5 files; `ClassPSPACE` 0 FAIL / 0 WARN over 2 files;
  `SpaceComplexity` 0 FAIL / 0 WARN over 42 files (`Hierarchy.lean`
  included; facades sit outside the per-tree linter, as in round 1).
* Statement-freeze baseline: commit `aa02db41`.
* The repaired surface's new declaration count: 14 definitions + 1
  (`Turing.Cfg.InWindow`) and 12 sorried statements, counts verified
  programmatically against the sweep log.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p43-r2-findings.md`; the gate closes on zero blockers and majors.
