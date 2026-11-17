# Gate kit: the checks behind a campaign gate

The scripts that produce a gate's evidence for a Lean PR. They take a PR head and a base, and:
1. replay the changed modules' downstream closure on an olean snapshot;
2. seal the changed proofs and run their controls;
3. run the proof-syntax and Lean-backed definition sweeps, and resolve citation homes;
4. run the copy screen;
5. assemble everything into the evidence files and data carrier that the audit bundle carries.

They were extracted from the Arora–Barak chapters 3–4 campaign (gates 121–158), where each gate
used a per-gate copy. Here every gate-specific value comes from one file, `$GATE/gate.json`.

Lean runs only through the wrappers in `devtools/seyoon/` (`leanelab.sh`, `leanelab-o.sh`,
`leanelab-i.sh`), never `lake build`. Several run at once within the pool of `leanpool.sh`:
min(nproc, MemAvailable / 4 GB), at most 5, shared through the lock slots under
`$TCSLIB_SCRATCH/locks`.

## Requirements

- A checkout of the repository (`repo`) in which **both the head and the base contain
  `devtools/seyoon/`**. The replay driver copies the tools from the head's tree. For a branch
  cut from `main`, merge the `seyoon-devtools` branch into it first.
- A scratch directory (`scratch`) holding:
  - the input olean snapshot `<scratch>/<input_snapshot>/` (a whole snapshot of the base);
  - its object map `<scratch>/manifests/<input_snapshot>.output.json` (relative path to SHA-256).
- The Lean toolchain (elan) and the checkout's `.lake/packages` with their oleans.
- Python 3.11 or later; run everything with `python3 -I`.

## `gate.json`

```json
{
 "repo": "/path/to/tcslib",
 "scratch": "/path/to/tcslib-scratch",
 "pr": "short label",
 "head": "<PR head commit>",
 "base": "<the merge target's Lean commit>",
 "baseline": "<same as base, unless the merge target has later records-only commits>",
 "merge_target": "origin/<branch the PR merges into> (defaults to baseline)",
 "input_snapshot": "oleans-xxxxxx",
 "output_snapshot": "oleans-clNNN-xxxxxx",
 "historical_timing": "<optional: an earlier replay's module-results.json, for scheduling>",
 "records_gate": "campaign/gates/NNN-name",
 "evidence_subdir": "evidence",
 "evidence_files": {"ExtraProbe.out": "probe/ExtraProbe.out"}
}
```

The merge target's Lean must equal the baseline's. The driver checks this, then replays the
prospective merge of the head into the merge target.

## Running a gate

```bash
export GATE=/path/to/scratch/gNNN        # a fresh folder holding gate.json
bash devtools/seyoon/gatekit/run.sh      # prepare, replay, checks, sweeps, screen, dispositions
python3 -I devtools/seyoon/gatekit/assemble.py   # then copy $GATE/records-payload into the repo
```

`run.sh` prints a summary: the replay verdict, the seals, the controls, the proof-syntax read
candidates, any probe that exited non-zero, and the copy-screen delta. It runs these steps:

| Step | Script | Output in `$GATE` |
|---|---|---|
| owners, populations, base sources, driver request | `prepare.py` | `CHANGED.txt`, `POPULATION*.txt`, `base-src/`, `driver-request.json` |
| declaration inventory (added, removed, statement and definition changes) | `mksource.py` | `SOURCE.json`, `SOURCE-base.json` |
| merged-tree replay | `driver.py` | `replay/` (`RESULT.json`, receipts, logs), the output snapshot `<scratch>/<output_snapshot>` |
| metadata, seals, controls, QA and lint deltas | `checks.sh` → `checks/*.py` | `metadata/`, `seals/`, `controls-part*/`, `qa/`, `checks.out` |
| Lean-backed definition sweep, citation probes | `pipeline.sh` → `defsweep/` | `defsweep/` (`SUMMARY.json`, logs), `dsw/` |
| copy screen | `screen.sh` | `screen/` (`pairdiff.txt`) |
| citation homes | `defsweep/cites-summary.py` | `defsweep/CITATION-HOMES.json` |
| pair dispositions | `dispositions.py` | `screen/PAIR-DISPOSITIONS.json` |

**A new head.** A failed check usually means a repair and a new head. Move the earlier outputs
aside into `runN/` (`replay`, `seals`, `metadata`, `qa`, `controls-part*`, `dsw`, `screen`, the
`*.out` and `*.log` files, `SOURCE*.json` and the defsweep logs), delete the output snapshot,
update `head` in `gate.json`, and run again. `assemble.py` carries every `runN/` folder in the
data carrier.

**Copy-screen pairs.** Every new or removed pair needs a disposition in `$GATE/pair-notes.json`,
keyed `"NEW|<target>|<source>"` (or `GONE|…`), with the value `[class, note]`.
`dispositions.py` stops on an unclassified pair.

## Reading the results

- **Seals** (`seals.out`): each changed or added proof is re-elaborated with every definition
  from another file that it reaches made irreducible. `FAIL` means the proof unfolds such a
  definition. Fix it by citing a reader lemma (for example, the `astep_*` lemmas or
  `timeConstructible_iff`) instead of `rfl`, `change` or projections through the definition.
- **Controls** (`controls-part*`): every sealed definition has a paired identity that passes
  natively and fails sealed. This shows that the seal really blocks it.
- **Proof-syntax sweep** (`checks.out`, "read candidates"): a definition from another file passed
  to `simp`, `rw`, `unfold` and so on in a changed proof. Each candidate is printed. Replace it
  with a reader lemma.
- **Lean-backed sweep** (`defsweep/SUMMARY.json`): the identifiers resolved by Lean. Foreign
  definitions from the core library or Mathlib are expected.
- **Citation homes:** the modules defining what the changed declarations newly cite. Bundle them
  for the auditor. A scope pass error `unknown namespace` in a `Cite_*` log is a known harmless
  kind.

## Templates (`templates/`)

- `MetadataBody.lean.txt`: the boundary metadata probe (`checks/metadata.py`).
- `Native.lean.txt`: the control probe (`checks/controls-half.py`).
- `prepare_boundaries.py`: its `clean` function is reused to strip comments before parsing.
- `irreducible.json`: heads that Lean already makes irreducible, so they have no native control.

## Other tools

- `blueprint/build_tcslib_graph.py`: rebuild the TCSlib part of `dep_graph.json` from `.ilean`
  files written by `leanelab-i.sh`. Other projects' entries are kept.
- `devtools/seyoon/stage.sh` stages a bundle on the exchange. With `STAGE_EXPORT=listed`, its
  final check exports only the bundled paths, which keeps it inside the disk allowance.
  `TCSLIB_STAGE_REPO` names the checkout it reads from; the default is
  `$TCSLIB_SCRATCH/wt-hk`.

## Validation

On 2026-11-17 the kit reran gate 158 round 2's run 4: head `bf6e26e8`, base `179c8c9c`, on
`oleans-cc91f4`. It reproduced that run's results:
- replay 129/129;
- seals PASS (8 proofs, 18 heads);
- controls 29/58;
- 0 read candidates;
- the copy screen unchanged at 25 pairs.
