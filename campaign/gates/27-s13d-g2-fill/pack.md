# External audit pack — §13d G2 fill gate: the mapped sweep rows and the cascade's new home (3 targets)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (Thm 3.1 at `f log f`, through the
Hennie–Stearns simulation of [AB09] §1.7). The §13d revision of the zone layer
(`machine-library-design.md` §13d) has a G2–G4 statement gate. It closed on 2026-10-14 with PASS
0/0/5 (`audits/s13d-g24-statements-findings.md`, resolutions `…-resolutions.md`), and its
statements landed in PR #106. That landing left three theorems sorried for the G2 fill.
**This gate covers the G2 fill, which proves them:**

| File | Target | What it states |
|---|---|---|
| `Build/Catalog.lean` | `Turing.copyMapTM_run_ofCfg` | the mapped copy's framed run: from any start with the source word delimited at the head, exit at exactly `2|w| + 2`, the destination interval holding `merge` of its old cells and the extracted source, everything else unchanged, both touched heads within one cell of their interval until then |
| `Build/Catalog.lean` | `Turing.transferMapTM_run_ofCfg` | the same for the mapped transfer, whose return pass also writes the residue `rest` over the source interval |
| `Build/Zone.lean` | `Turing.zoneCascadeRight_home` | under the classical pre-state of `Turing.zoneSide_cascadeRight`, the cascade's new home is the right word's first cell |

**The maintainer did this fill, not a fill agent** (user decision 2026-10-15: "Maintainer
finishes, then PR"). There is no delivery and no brief; the gate's rulings and obligations are the
contract. It is PR #108 (`lean/g2-fill`), with two commits:
- `8e3cee48`, the fill;
- `a9ee4701`, the Zone factoring the user chose after the first copy screen.

It was merged on 2026-10-15 as `b6e0344c`, after the user's replay, and is Lean-identical to
the replayed head.

**Every proof is kernel-checked.** The replay and axiom evidence is below. Every public of both
files prints standard axioms only. Fill gates close on zero blockers and zero majors
(`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.
The standards are attached.

## The contract from the statement gate

- **Ruling 7:** "One trace family at the G2 fill. The plain framed rows derive from the proved
  mapped rows, and proved plain theorems are never retargeted to admitted mapped results
  meanwhile."
- **Obligation 2:** G2's fill comes only after MIG-1 stage S. Then the cascade-home lemma.
- **Obligation 4:** F-D must not unfold the copy or transfer tables by name.
- **Minors 1 and 2** were carried to G5's statement phase. They do not bind this fill.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | the three targets |
| **Other public bodies** (statements byte-identical) | Catalog: `transferTM_run_ofCfg`, `copyTM_run_ofCfg` (the mapped rows at the identity map, ruling 7), `transferTM_spaceUsedByTape`, `copyTM_spaceUsedByTape` (through the mapped trace at the identity map). Zone: `zoneSide_cascadeRight` (a projection of the shared induction), `zoneCascadeRight_lengths` and the regression `zoneCascadeRight_zero` (cite the two new helpers) |
| **Moved** | Catalog's mapped framed block (`copyMapTM_plain`, `transferMapTM_plain` and the two mapped framed rows, whose bodies are the targets) moves from the end of the file to just before `transferTM_run_ofCfg`, so that the plain rows can cite it; the two `_plain` lemmas are byte-identical |
| **Privates removed** | Catalog: `catalogCopyF`, `catalogCopyR`, `catalogTransferR`, `catalog_copy_forward`, `catalog_copy_trace`, `catalog_transfer_trace` |
| **Privates added** | Catalog: `catalogSweepF`, `catalogSweepR`, `catalogSweepResidueR` (value-parametric families), `catalog_transferMap_trace` (the one trace), `catalog_trace_clauses` (the trajectory clauses of a framed two-pass row, from its trace), `copyMapTM_step_eq`, `copyMapTM_runFrom_eq` (the copy is the transfer with residue `some`). Zone: `zoneCascadeRight_zero_eq`, `zoneStepPair_below`, `zoneStepPair_pre`, `zoneCascadeRight_classical` |
| **Imports** | unchanged |
| **Docstrings** | Zone's module status "proved"; the G2 section header; five proof sketches name what the formal proofs instantiate or share; every new private has a docstring, and each nontrivial proof a sketch (the two two-line proofs, `copyMapTM_runFrom_eq` and `zoneCascadeRight_zero_eq`, explain themselves in the docstring) |
| **Size** | Catalog 12,874 → 12,977 lines; Zone 1,324 → 1,388 |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached base files (`…/gate/Catalog.base.lean.txt`,
   `…/gate/Zone.base.lean.txt`, at `83a463ee`), the head files and the patch (`…/gate/pr108.patch`).
   - Every public statement is unchanged.
   - The only public bodies that changed are the three targets and the seven in the table above.
   - The private changes are exactly those listed.

   `logs/freeze-{catalog,zone}.log` is the maintainer's record.
2. **Ruling 7, one trace family.**
   - Check that `catalog_transferMap_trace`'s two families describe the transfer's forward and
     return passes:
     - the forward family writes `merge (old destination cell) (extract source cell)` at offset
       `r`;
     - the return family has rewritten the crossed source suffix to `rest`.
   - Check that the trace is the only one either mapped row cites.
   - Check that the plain framed rows and plain space lemmas cite the mapped rows at
     `extract := id`, `merge := fun _ s => s`, and, for the transfer, the blank residue.
   - Check that no proved plain theorem rests on an admitted result at any point. The axiom walks
     are attached.
3. **The copy as a transfer.**
   - `copyMapTM_step_eq` states that the mapped copy's step function equals the mapped
     transfer's at the identity residue `some`. In other words, the transfer's return pass writes
     back exactly what it reads.
   - `copyMapTM_run_ofCfg` is then the transfer's row, with the residue normalized by
     `o.bind some = o`.
   - Confirm the claim and the sketches that describe it. This is the step that removed the
     separate copy trace.
4. **Zone.**
   - `zoneSide_cascadeRight` and `zoneCascadeRight_home` are the two projections of one induction,
     `zoneCascadeRight_classical`.
   - Its successor case cites `zoneStepPair_pre`, the pre-state descending one level, which cites
     `zoneStepPair_below`.
   - Its zero case cites `zoneCascadeRight_zero_eq`. That lemma is proved by
     `show zoneMove true z = _`, since `List.range 0` reduces.
   - **Rule** whether it is acceptable to re-point the round-2 regression `zoneCascadeRight_zero`
     at the shared unfolding lemma. Its statement is unchanged; its proof no longer unfolds the
     cascade itself.
5. **Duplication** (failure mode 5). The v3 screen covers the G2–G4 gate's five files and
   `Simulation`, with base and final logs and the whole population attached.
   - The pairs go from 384 to 369, and the reproduced text from 124,738 to 116,324 characters.
   - 18 pairs are gone, including the base's 91% `catalog_transfer_trace` ↔ `catalog_copy_trace`.
   - **Three pairs are new by name, all in-file, and the user approved all three on 2026-10-15**
     (`NOTES.md` §3, `logs/pairs.log`):

     | Pair | Overlap | Kind |
     |---|---|---|
     | `catalog_transferMap_trace` ← `catalog_clear_trace` | 67%, 1,086 chars | successor of the base's 54% pair: the sweep-trace tactic idiom |
     | `catalog_transferMap_trace` ← `catalog_write_take` | 50%, 62 chars | two idiom fragments |
     | `zoneCascadeRight_lengths` ← `zoneStepPair_below` | 54%, 314 chars | successor of the base's 53% pair: calls to the same two lemmas |

     Verify the accounting and the successor claims.
   - **The maintainer's own review** found one near-restatement that the text screen does not
     report. `clearTM_run_ofCfg` still derives its trajectory clauses inline. These are the clauses
     that the new generic `catalog_trace_clauses` provides, with `touched := (· = i)`. This
     predates the fill and is unchanged by #108. **Rule** whether it is debt under failure mode 5.
6. **Documentation.**
   - Check each sketch and each new private's docstring against its proof.
   - Check Zone's status line and the G2 section header.
   - Check the "Formally …" sentences added to the plain rows' sketches.
7. **Downstream.**
   - `Build/Contract/Catalog.lean`'s `copyMapTM_contract` and `transferMapTM_contract` are built
     from the two mapped framed rows, which are now proved.
   - The replay's sorry counts drop from 2 to 0 for Catalog and from 1 to 0 for Zone; nothing else
     changes.
   - **Obligation 4:** outside `Build/Catalog.lean`, no Lean file unfolds `copyTM`, `transferTM`,
     `copyMapTM` or `transferMapTM` by name (a `grep` at the head; attestation). Inside it, only the
     trace lemma and `copyMapTM_step_eq` do.
8. **Records.** Check `NOTES.md`, the backlog entry (RD-5, "Next") and this pack against the
   evidence. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

- **Process.**
  - The maintainer wrote both files with asserted generators (`scripts/mkoverlay.py`,
    `scripts/mapped-block.lean.txt`, `scripts/mkzone.py`).
  - Re-running them on the files at `83a463ee` reproduces the PR head byte for byte.
  - Lean was run only through the throttled `scripts/leanelab.sh` (no olean output).
  - Python ran only as `python3 -I`.
- **Elaboration** (against `oleans-lcanon4`; the outputs are the axiom probes, which are each
  final file with `#print axioms` appended):
  - Catalog: 0 errors, 0 sorry warnings, 78 warnings. The base has 92; 0 are new and 14 removed,
    keyed by message and source line (`logs/warnings-catalog.log`).
  - Zone: 0 errors, 0 warnings. The base's one warning was the sorry.
- **Axioms** (`logs/elab-*-final-with-axioms.out`): every public, 95 in Catalog and 65 in Zone,
  prints a subset of `[propext, Classical.choice, Quot.sound]`; none prints `sorryAx`.
- **Replay** (run by the user; fresh `.oleans` from `oleans-lcanon4` into `oleans-lg2`;
  `…/gate/replay-lg2.log`, script `…/gate/replay-lg2.sh`): 87 of 87 modules, 0 errors. The
  only sorry counts that moved are `Build/Catalog` (2 to 0) and `Build/Zone` (1 to 0).
- **Lint** (`logs/lint-*.txt`):
  - `campaign_style_lint.py` on `Build/`: 0 FAIL at base and head. The WARN sets are equal apart
    from the two size warnings' line counts.
  - `style_lint.py` on the two files: 50 findings at the base and 49 at the head, none new.
- **Hygiene** (`logs/hygiene.log`): 0 hits in the 496 added lines.
- **Widths:** no new line over 100 characters.

## Bundle

`s13d-g2-fill-bundle.md` contains, one section per file:
- this pack;
- the standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`);
- the G2–G4 statement gate's pack, findings and resolutions;
- the design note `audits/evidence/s13d/g24/G24-design.md`, and `machine-library-design.md`,
  `backlog.md` and `AroraBarakChapters3-4Plan.md`, whole at the tip;
- the evidence folder `audits/evidence/s13d/g2-fill/` (notes, generators, probes, logs,
  `SHA256SUMS`, the replay order), and its `gate/` subfolder (the two base files, the PR's patch,
  the replay script and its log);
- the screen `audits/evidence/retrofit/copy-text-screen-v3.py` and the two lint scripts
  (`scripts/campaign_style_lint.py`, `scripts/style_lint.py`), so that those checks can be rerun;
- the screen population at the merged tip: `Build/Catalog.lean`, `Build/Contract/Catalog.lean`,
  `Build/Zone.lean`, `Build/ZoneTape.lean`, `Build/ZoneRebalance.lean`, `Simulation.lean`;
- `Configuration.lean`, for `Action.apply` and `Cfg`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s13d-g2-fill-findings.md`. The gate closes when it has zero blockers and zero majors.
