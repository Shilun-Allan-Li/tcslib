# NOTES: copy-text screen v3, the same-name residual fixed (Diagonal Part 1 gate, m2)

**Source:** minor m2 of the Diagonal Part 1 statement gate (`audits/diagonal-p1-statements-findings.md`).
Both v1 and v2 skip a pair whenever `(file, extracted name)` coincide. So two distinct
declarations in one file with the same short name are never compared. This residual was already
recorded at v2 (`../NOTES.md`, "Residual finding"), where the fix was deferred to the next
baseline reset. The gate's mutation makes it concrete: the received
`Complexity.time_hierarchy_of_pos` proof is restored beside the generic
`Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos`. Both are written
`theorem time_hierarchy_of_pos`, in one file, and the reported result does not change. No Lean
was run for this note.

## The fix: `audits/evidence/retrofit/copy-text-screen-v3.py`

SHA-256 `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`. The changes from
v2 are in `v2-to-v3.diff`.

- **Identity:** each declaration is identified by `(path, source offset)`. A pair is skipped only
  when both sides are the same declaration.
- **Labels:** the v2 label `<file>::<name>` when the extracted name is unique among the file's
  screened declarations. Otherwise, the namespace-qualified name, and `#k` (k-th in source order)
  if that is still repeated, as for anonymous instances (whose extracted "name" is `:`).
- **Namespaces:** tracked through `namespace`, `section`, `noncomputable section`, `mutual` and
  `end`. A dotted `namespace A.B` opens two scopes and may be closed by `end B`, `end A` or by
  `end A.B`, as in Lean. `_root_.` is honoured. An `end` that closes no matching scope stops the
  screen.
- **Equivalence:** where no file in the argument list repeats a screened short name, the labels,
  the skip test, the tuples, the sort and the totals are v2's, so the output is byte-identical
  to v2's. Otherwise v3 differs from v2 exactly by the pairs between same-named declarations of
  one file (what `../samename.py`-style scans list) and by those declarations' labels.
- **Output format:** unchanged. `tools/screendelta.py` and `tools/pairdiff.py` parse it unchanged.

## Checks

| Check | Result |
|---|---|
| Scope parse over the tip `ff4cab18`, all 723 Lean files (`parsecheck.py`, `parsecheck-tip-ff4cab18.out`) | every `end` closes its scope; 2 files end inside a namespace (legal) |
| Regression control (`regression-control-v3.sh`, output `regression-control-v3.out`): one file with `N1.dup`/`N2.dup`, a generic `A.B.gen` beside `A.gen` (dotted namespace closed by `end B`, `end A`), and two anonymous instances | v2: 0 pairs. v3: all 6 pairs (the three pairs both ways), no self-pair. **PASS**, exit 0. With v2 in both roles it fails, exit 1 |
| The gate's mutation (`audits/evidence/diagonal-p1/scripts/negctl.sh`, control `screen-restore`) | v2: 16 pairs, 3,277 characters, unchanged. v3: 18 pairs, 3,667 characters, the new pair both ways (86%, 83%). **PASS** |
| Diagonal Part 1's before and after populations (7 files each) | v3 = v2 byte for byte; the pair lists equal the gate's v1 logs |
| Record tables cont5 base (`1b6b972c`, 43 files, contains `Build/CfgRecord.lean`; `equivalence-w1-cont5-1b6b972c.txt`) | v2: 2,428 pairs, 790,157 characters. v3: 2,430, 790,289. The diff is exactly the predicted one: CfgRecord's instance pair both ways (`Turing.{k#1`, `#2`, 66/66), and `Contract/Basic`'s repeated `trans` relabelled `Turing.Segment.trans` in its two pairs |
| Same-name pairs at the tip `ff4cab18`, all 723 Lean files (`../samename.py`, `samename-tip-ff4cab18.txt`) | 11 same-file same-name groups (22 declarations); 2 pairs meet the threshold, both CfgRecord's `Fintype`/`DecidableEq` instance pair, already recorded |

## Consequences

- **No recorded result needs a correction.** At the tip, the only pair v3 adds anywhere is the
  CfgRecord instance pair, accepted as an instance idiom in `backlog.md` at v2. In any population
  containing `Build/CfgRecord.lean` it appears on both sides of a before/after screen, so it is
  never reported as new. Earlier trees were scanned at v2 (`../NOTES.md`: 252 files at
  `2c3c975a`, and the B5a cont3, record tables cont5 and §13d trees) with the same single pair.
- **Future briefs and gates use v3.** A v3 after-screen can be diffed directly against a v2
  before-screen, or a v1 one where basenames are distinct, except in files that repeat a short
  name. There the labels are qualified, so re-run such a base with v3 before diffing.
- **Diagonal Part 1** uses v3 from its closing commit (`audits/diagonal-p1-statements-resolutions.md`).
