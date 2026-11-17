# DW-10 handoff: recorded seal debt in Complexity-library files

The Pass–shelat campaign's seal-debt inventory (DW-10) found recorded Rule 10 items in 21 files of the Complexity
library, outside the campaign. Seyoon ruled on 2026-11-17: "Arora–Barak material that needs fixing: send me a pasteable
prompt I can give to a different chat. You are responsible for any seals from cryptography content." This folder is
that handoff: the items (`items.tsv`), these notes, and the prompt for a separate chat (`prompt.md`). The campaign's own
inventory job (`../issued-r1/`) does not seal or scan these files; it carries their items as HANDED-OFF.

## What a Rule 10 seal is

Rule 10 (`policy.md` §1, *Definitions land with their lemmas*): a proof reads another file's TCSlib definition only
through the lemmas published beside it (its equation `_eq`, `_apply`, `_iff`, `simps` projections, case lemmas or
contract), never by unfolding it. Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step but are
never passed to `simp`, `rw` or `unfold`. Reducible abbreviations are notation and are never sealed.

A **whole-file seal** checks this mechanically. A probe module holds the file's own source bytes behind a harness that
installs `attribute [local irreducible]` on every ordinary TCSlib definition of the file's transitive import closure
(kind `def`, a matcher or not reducible), with install and EOF records that state how many requests were installed
and verified. The probe is elaborated with `lean -DmaxErrors=0` (Lean's default cap of 100 errors once truncated a
`CodeSimulator` seal: finding C-F02). Every error is a place where the proof relied on unfolding a foreign definition.
Explicit reads (a foreign definition passed to `simp`, `rw`, `unfold` or `delta`) do not always fail under a seal, so
an **explicit-unfold scan** lists them separately; a third check lists stored proofs that reference a foreign
definition's generated equation (`eq_1`, `eq_def`).

**Variants.** **A** treats `Complexity.PolyExpr.eval` as notation (ruling of 2026-11-07); **B** seals it too. **Strict**
seals the projection-coercion instance `FinDist.instCoeFunForallReal`; **coe** treats it as notation (Q3, Seyoon
2026-11-17). **Coe-A is canonical**: a failure only under B or only under strict is recorded, not fixed (B-only items
go to Seyoon for a ruling; strict-only ones need nothing).

## The canonical tooling, by path

- `scripts/lean_check_tree.sh`: one module per `lean` process into a scratch olean tree (`lake build` is banned).
- The seal suite as the campaign's DW-5 job ran it: `briefs/pass-shelat-ch5-8/maintenance/dw5/dw5-evidence.zip`
  (SHA-256 `12abc05a61c08de7cb38b9d3bccdea5b3dd44dff6f65f036a50584a39e1dd630`), under `dw5/tools-used/`:
  `seal/rule10_b.sh` (the driver of the four variants and the controls), `seal/runner_full.py` (`lean -DmaxErrors=0`,
  no `-o`), `seal/review/mkcollect.py` with `NmCollect.template.lean` (the collector: definitions, closures, stored
  constants), `seal/review/mkseals_ab.py` (strict; `SEAL_EVAL=1` gives B), `seal/review/mkseals_coe.py` (coe),
  `seal/review/sealsum.py`, `seal/review/ctlcheck2.py`, `seal/review/touched.py`, `seal/review/archived-gate10-tools/`
  (the instrumenter, used unmodified), `seal/scan1_g40.py` and `seal/scan2.py` (the explicit-unfold scan),
  `rule10_dw5.sh` and `mkctl_dw5.py` (an owner-level driver and a paired-control generator). DW-5's
  `briefs/pass-shelat-ch5-8/maintenance/dw5/README.md` shows a complete run.
- The most recent adaptation of the same suite: branch `exchange/pass-shelat-ch5-8` at
  `d929cc21ec817b2518d57a7262e42744728f029a`, `inbox/fills/bb1-sim-statements/evidence/tools/` (`drivers/rule10_stmt.sh`
  and `seal/`).
- `SEAL_CHUNK` splits request sets above about 2,500 rows (one harness command overflows Lean's stack at 2,921).

## How items are fixed

By **readers** added next to the definition being read (an equation or case lemma, a formula docstring, no
`@[simp]`), then the failing proof re-derived through them; or by a **proof-only re-derivation** through readers that
already exist. **No statement changes**: a failure that sits in a declaration's statement is reported, not fixed.

## The items (`items.tsv`)

608 rows, one per recorded item located in the 21 files at the campaign base `f472accd5e000a53d0fbe02b5414435429ce4a70`
(Lean equal to `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b`). Columns: `item_id`, `source`, `kind`, `file`,
`declaration`, `detail` (line and message or item at the record), `reads` (the definition read and its home module,
where the record gives it), `record_status`, `record_path` (the record in this repository; a `.zip:` path names the
entry). Sources:
- **#248 historical observations** (`H:<row>`, 9): the PR #248 ledger's original rows, with #248's disposition.
- **#248 current observations** (437): what the ledger retained at #248's merge: `SEAL-…` seal diagnostics (161),
  `C1-…` explicit reads (275), `C3-…` generated-equation reads (1).
- **Provider pairs** (`EFF72:`/`LEV52:`, 102): proofs in these files that two campaign fills cite (the efficiency fill
  #285 and the Levin padding proof #286) under Seyoon's 2026-11-10 provider rulings, with both ends: the failing
  declaration here and the citing fill. Each repeats a `SEAL-…` row of the current observations (53 distinct
  diagnostics).
- **SY-F07** (2): `CircuitComplexity/Uniform`'s 4 canonical-A failures in 2 declarations (readers such as
  `isFaninTwo_iff` now exist).
- **C-F02** (58): `TuringMachine/CodeSimulator`'s 177 seal errors in 58 declarations, identical in all four variants
  (1,232 requests).

The records are at #248's head or later revisions; files have moved since, and the `file` column is the static
location at the base. Line numbers are the record's.

## Counts per file

| File | #248 historical | #248 current | provider pairs | SY-F07 | C-F02 | Total |
|---|---|---|---|---|---|---|
| `Complexity/CircuitComplexity/PPoly` |  | 7 |  |  |  | 7 |
| `Complexity/CircuitComplexity/Uniform` |  |  |  | 2 |  | 2 |
| `Complexity/ClassNP/PolyTime` |  | 8 | 12 |  |  | 20 |
| `Complexity/ClassNP/PolyTimeBlockLoop` |  | 24 | 1 |  |  | 25 |
| `Complexity/ClassNP/PolyTimeBlockTests` |  | 2 |  |  |  | 2 |
| `Complexity/ClassNP/PolyTimePairing` | 9 | 4 | 7 |  |  | 20 |
| `Complexity/ClassNP/PolyTimePrefix` |  | 4 | 2 |  |  | 6 |
| `Complexity/ClassNP/Reductions` |  | 39 |  |  |  | 39 |
| `Complexity/ClassP/BinaryArith/AddSub` |  | 16 |  |  |  | 16 |
| `Complexity/ClassP/BinaryArith/Words` |  | 12 |  |  |  | 12 |
| `Complexity/ClassP/P` |  | 4 |  |  |  | 4 |
| `Complexity/Randomized/Adleman` |  | 2 |  |  |  | 2 |
| `Complexity/Randomized/PolyTimeModel` |  | 21 |  |  |  | 21 |
| `Complexity/Randomized/SipserGacs` |  | 13 |  |  |  | 13 |
| `Complexity/TuringMachine/Build/Convention` |  | 2 |  |  |  | 2 |
| `Complexity/TuringMachine/Build/Wrappers` |  | 81 | 40 |  |  | 121 |
| `Complexity/TuringMachine/CodeSimulator` |  |  |  |  | 58 | 58 |
| `Complexity/TuringMachine/Deterministic` |  | 8 | 2 |  |  | 10 |
| `Complexity/TuringMachine/Encoding` |  | 13 |  |  |  | 13 |
| `Complexity/TuringMachine/Simulation` |  | 96 | 38 |  |  | 134 |
| `Complexity/TuringMachine/UniversalBlock` |  | 81 |  |  |  | 81 |
| **Total** | 9 | 437 | 102 | 2 | 58 | 608 |

