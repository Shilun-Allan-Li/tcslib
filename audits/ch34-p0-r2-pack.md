# External audit pack — Chapters 3-4, phase P0, round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P0, round 2.
Round 1 (`audits/ch34-p0-findings.md`, attached verbatim) returned 0 blockers, 1 major,
7 minors, 2 notes; per `workflow.md` §3 the gate did not close. This round audits the
repairs. The gate closes on zero blockers and zero majors.

## Brief for the auditor

You have the round-1 report. For each finding, the table below states the repair and
where it lives; the complete change is the attached diff. Your deliverables:

1. For **finding 1 (the major)**: verify that the adopted convention and its
   machine-checked anchors dispose of it — the collapse is now documented at the
   definition site, every planned asymptotic chapter statement is positive-normalized
   (including the restated Ex 3.2), and the sanity statements S1-S6 pin the
   characterization. The sanity statements are **sorried**: audit them as statements
   (true as stated? correctly scoped?), exactly like any statement-phase audit. Their
   proofs are fill work; round 1 already settled the underlying mathematics.
2. For each **minor**: verify the repair matches your proposed fix or say why the
   deviation is inadequate.
3. Report anything the repairs broke or newly misstate, in the same findings-table
   format and severity scale as round 1.

## Scope

| Item | Where |
|---|---|
| Under audit | the diff `84b79daf..2ca970cd` (attached), restricted to: the repaired received files, `SpaceComplexity/ZeroSpace.lean` (new), `SpaceComplexity/Basic.lean` (convention bullet), `TuringMachine/CounterProgRun.lean` (headline + S9), the plan's §1/§2.4 statements, and the evidence-provenance repair |
| Declared, out of scope | the same commit range also contains the phase-P3.1/P4.1 statement skeletons (`TuringMachine/{OracleFinite,OracleNondeterministic,NondeterministicSpace}.lean`, `ClassOracle/*`, `SpaceComplexity/{NSPACE,SpaceClasses,Constructible,Inclusions,Examples}.lean`; 24 sorried statements) and the `machine-library-design.md` §12 addendum. These receive their own statement-phase audits and are listed here only so the diff holds no surprises. Also out of scope: tactic proofs; round-1 items the auditor marked "no change required" (notes 9-10) |
| Source text | as in round 1 |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **major** — zero of `s` collapses `SPACE s`; literal `SPACE(n)` is the wrong class | Convention adopted (maintainer-verified derivation first: `visitedByTapeHead` images the nonempty `range (t+1)`, so `k ≤ spaceUsed` always): every asymptotic chapter statement uses everywhere-positive bounds; plan §2.4 records it and §1 restates Ex 3.2 as `SPACE(n+1) ≠ NP`; `SpaceComplexity/Basic.lean` documents the collapse at the definition site; **`SpaceComplexity/ZeroSpace.lean`** adds S1-S4 + S5 + S6 as sorried statements with sketches (`k_le_spaceUsed`, `ComputesInSpace.k_eq_zero_of_exists_zero`, `SPACE_eq_zero_of_exists_zero`, `SPACE_id_eq_SPACE_zero`, `SPACE_succ_of_pos`, `SPACE_succ_eq_max_one`, `pairEncode_bits_inj`, `trueLang_mem_SPACE_zero`, `evenLang_mem_SPACE_zero`). The frozen `SPACE` definition is unchanged, per your proposed fix |
| 2 | minor — `sim_run` headline overstates | Headline now states the start-`t`-below-`B` hypothesis; the broader interface is the new sorried `sim_run_of_regs_le` (S9) with per-step cost `2B + 5` (pre-step valuations `≤ B`, mid-step increment `≤ B + 1`, `sim_step` at `B + 1`) |
| 3 | minor — `Mode`/`callSegs` pair-shape claim | Zero-argument qualifier added at both the Main-definitions bullet and the `Mode` constructors; the legitimate no-argument behavior is kept |
| 4 | minor — `valP`/`valQ` canonical payloads | Constructor docstrings now require canonical `Nat.bits` payloads, with the `pairEncode [] [false]` rejection named |
| 5 | minor — `lenEq`/`lenLe` totalization | Both docstrings now state the default-`[]` projections and that malformed words (e.g. `[]`) are members |
| 6 | minor — `ReachesB` "throughout" | Docstring now says strictly-before-the-endpoint, names the `T = 0` reflexive instance, and points consumers at `Reaches.toB` |
| 7 | minor — sweep-log provenance | The attached round-2 sweep log opens with the commit recorded **at start** (`2ca970cd`, full hash, branch, wipe statement). Round-1 erratum acknowledged: that log's trailing revision was read at completion, after a documentation-only commit moved HEAD; `git diff --stat 84b79daf e64cec9e` is 1 file (+128), `machine-library-design.md` only — no Lean source differed |
| 8 | minor — phantom exports | `ARMSim.lean` now lists the per-instruction `sim_*` lemmas and points to `arm_run` in `ARMRun`; `Compile.lean` lists singular `CallOK` with its `hcalls` role; `Layout.lean` points to `Machines.Sim`/`CallReturn`/`Call` in place of the nonexistent `Machines.Gadget` |
| 9-10 | notes | No change, per the report |

## Repository-side attestations (verify or challenge)

Produced at commit `2ca970cd` (= the diff's right endpoint; the working tree at sweep
time was clean apart from untracked local scratch directories, as the log header
records).

* **Fresh elaboration sweep** (`audits/logs/ch34-p0-r2-sweep.log`): scratch olean tree
  wiped, then all **101** modules — the received closure, its dependency delta, and the
  new campaign modules — in dependency order: 101/101 pass, 0 `error:` lines, 101 fresh
  `.olean`s, and **exactly 34** `declaration uses 'sorry'` warnings, matching the
  declared inventory (24 phase-P3.1/P4.1 skeleton statements + 9 `ZeroSpace` sanity
  statements + 1 `sim_run_of_regs_le`); per-file counts: ZeroSpace 9, ClassOracle/
  Classes 6, Inclusions 4, SpaceClasses 3, SATOracle 3, NondeterministicSpace 2,
  NSPACE 2, Constructible 2, OracleNondeterministic 1, CounterProgRun 1, Examples 1.
* **Style lint** (`audits/logs/ch34-p0-r2-stylelint.log`): 0 FAIL across the
  SpaceComplexity (35 files), TuringMachine, ClassNP, ClassOracle and TimeHierarchy
  trees; the only WARNs are the pre-existing recorded size-exception files, none
  received, none new.
* **Received-file admissions**: of the 44 round-1 received files, the only one that now
  contains a `sorry` is `CounterProgRun.lean` — the single requested S9 statement.

## Findings format (as round 1)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in round 1. Findings go verbatim into
`audits/ch34-p0-r2-findings.md`; the gate closes on zero blockers and zero majors.
