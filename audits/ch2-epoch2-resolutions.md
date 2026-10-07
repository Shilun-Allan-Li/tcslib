# Chapter 2, epoch-2 fill gate — resolutions

**GATE CLOSED (2026-10-05). PASS in one round: 0 blockers, 0 majors, 2
minors, 11 notes** (`audits/ch2-epoch2-findings.md`). The auditor
independently rebuilt the full 57-module order from empty oleans at the
pinned toolchain, reproduced the closure program, and **extended
coverage to all 386 source privates and 1,167 private/generated kernel
declarations under the five owned modules — zero admission roots,
exactly the standard axiom triple** (finding 11). The audited bundle is
byte-confirmed: its reported SHA-256
`a85ad53cc29087b4e115f6621ea15625c46df144a74ba01ae4b49f19ea4ef588`
matches the committed `audits/ch2-epoch2-bundle.md`. The pack and the
dispatched briefs are immutable; both minors are recorded here as
errata, per protocol. Chapter-2 ledger: **38 of 59** original
admissions proved; Theorems 2.6 (both directions) and 2.9, Exercise
2.1, and the HALT pair end-to-end machine-checked.

## Minor 1 — erratum to `briefs/ch2-e2cont-batchC.md` (brief, not proof)

The brief's target-2 instruction "finish through target 1's paired
decider" is **wrong as written**: target 1's `pairedVerifier C c V`
tests exact width `|u| = C(|x|+1)^c` and membership of the
concatenation `x ++ u`, while target 2 requires the **original**
upper-bound test `|u| ≤ C(|x|+1)^c` and membership of `pairEncode x u`
in the supplied language (auditor's separating instance: `C = 1`,
`c = 0`, `x = u = []`, `V = {pairEncode [] []}`). **The delivered proof
is correct**: `paddedVerifier_mem_P` invokes the original paired
verifier after the shifted split, marker strip, and original-bound
check — exactly the right interpretation, chosen and documented by the
fill agent (`audits/ch2-epoch2-agent-reports/batchC-cont.md`, "Reverse
padded verifier"). No proof or statement change. Corrected reading, for
any future consumer of that brief: **the final call is the original
paired verifier on the reconstructed `pairEncode x u` under the
original upper bound, never target 1's exact-width predicate.**

## Minor 2 — erratum to the pack's E5 description: live/dead inventory

The pack grouped checkpoint helper families as "superseded by the
continuations' library-based routes." The auditor's kernel dependency
walk (finding 10) corrects this; the following inventory is **binding
on E5 execution**:

**Live checkpoint routes (still consumed by final closures — these are
finished, audited, clean contracts, not dead code):**

| Final theorem | Live checkpoint route |
|---|---|
| `NP_subset_EXP` | `enumDecider` → `enumLoop_run` |
| `HALT_NPHard` | `fixedPair_polyTime` → timed fixed-prefix construction → `prefixTM` |
| `timeConstructible_poly` | `poly_unary_computes` → `polyUnaryTM` |
| `TMSAT_NPHard` | exact unary deadline emission → `poly_unary_computes` / `polyUnaryTM` |

**Dead (absent from every final target closure):** `enumCarryTM`,
`enumCaptureTM` (absent from `NP_subset_EXP`'s closure), `choiceCopyTM`
(absent from the forward inclusion's closure).

The subsumption of 2C's *promotion requests* by library entries P3/P6
never meant the existing clients were rewritten. **E5 discipline, as
approved with qualification:** deleting a dead family, replacing a live
implementation with a catalog instance, and relocating a family are
three distinct changes. A live replacement requires reviewing the timed
and configuration contracts before deletion and rerunning client
closures; byte-identical relocation is not the applicable correctness
argument for a changed implementation. E5 remains serial and
post-gate.

## Dispositions — approved as qualified

- **E5**: approved-deferred with the inventory and discipline above.
- **D7 extension** (EXP 2,887 / Nondeterminism 2,627 / TMSAT 1,908):
  approved to trail; nothing forces a split before the E3 fills.
  **Binding on execution** (finding 12): the full D7 discipline carries
  over — byte-identical relocation plus ordered-sequence comparison
  does not solve cross-file access to private names, so keep dependent
  private families together or separately review any
  visibility/interface change; re-run the module-order sweep, target
  closures, the all-private/generated traversal for these five files,
  and the kernel export inventory; coordinate E5 replacements
  separately from moves so a changed route is never represented as
  relocation.
- **D6**: remains appropriately deferred (finding 13); no promotion is
  a prerequisite of this gate; when executed, retain all hypotheses and
  tape/head/output preservation conclusions and check clients before
  replacing private copies.

## Provenance qualifications (finding 11, accepted as stated)

The auditor independently established the source freeze, the final
sweep/axioms/lint, and the helper closures; the all-nine
checksum/replay executions, the three integration commits' contents,
and the interim 32→29→23 runs remain corroborated **maintainer
attestations** (the bundle carries reports, not archive payloads), with
no contradictory evidence. These stand on the committed per-integration
records and logs.

## Swept in the closing commit

- `scripts/style_lint.py`: the declaration regexes accepted only
  `noncomputable private` modifier order and so missed
  `private noncomputable def tmsatWrapperOutput` (finding 11,
  attestation-5 qualification — a lint display limitation, never a
  missing helper). Fixed to accept both orders; lint now reports
  TMSAT at 87 privates, matching the kernel inventory
  (`audits/logs/ch2-epoch2-close-lint.log`, still 0 FAIL / 3 WARN).

## Post-gate queue (now unblocked, serial, in order)

1. **D6** promotions (`timed_input_bound` → run calculus,
   `timed_rewind` → `Simulation.lean`).
2. **D7** splits (`Loop`, `Primitives`, now also the three ClassNP
   files), ride-along audited, under the qualifications above.
3. **E5** dedup under the live/dead inventory above.
4. E3 briefs (padding cluster, `EXP_subset_NEXP`, SAT track, Snapshot
   locality).
