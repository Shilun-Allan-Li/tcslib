# Rule 10 M0 preparation — ROOT ONLY execution

Status: PREPARED, NOT RUN. No Lean/lake/build process was started by this subagent.
No source, canonical tool, Git state or live worktree artifact was edited. The only
execution was text-only Python snapshot generation/AST parsing. Current working bytes
are NOT yet claimed equal to HEAD. First push remains pending.

## Inventory and scope

`snapshot/modules.txt` enumerates every currently present owned module: all FE files
including facades, Pairing.Exponents, Pairing.Linear, Pairing.MatrixDH and its children.
The current snapshot has 72 modules, 356 public written defs, 31 public written abbrevs,
47 structures and 40 named instances. All 387 defs/abbrevs have reader CANDIDATES; their
actual Lean names, theorem kinds and target occurrence in reader types are unverified.

The source declaration parser is only a text inventory. The canonical collector ROOTs
include ALL stored constants (constructors, eliminators, projections, matchers, instances,
private artifacts), without an algorithm-interface exclusion. ReaderCatalog adds the
native definition/projection/instance/matcher/proof-valued census. Instances and generated
record constants remain explicit inventory rows. Parent clarified that policy does not
require ordinary doc/readers for instances; they are not ordinary algorithm-control gaps.
Written defs/abbrevs are the paired-control priority. Abbrev/type-alias sensitivity limits
are marked, never called passing ordinary-definition tests.

Rerun snapshot preparation AFTER all PHFE/Adapter, Security, Headlines and future facade
files have been integrated and M0 source is frozen. Current list automatically discovers
new modules on rerun. Do not reuse this provisional 72-module list as final coverage.

## Pins and provenance

The unchanged suite is at evidence/preparation/tools/, from exchange source pin
bc9d982b83cb35ea351e2fb373752e8688945b1c. Existing provenance table is authoritative:
`evidence/preparation/tool-provenance.tsv`. prepare.py validates every prepared tool and
the wrapper against that table BEFORE importing the reviewed pure lexer. It records all
actual bytes in snapshot/tool-fingerprints.json. No canonical tool was changed here.

Only the previously authorized runner host adaptations exist: runner_full.py and
review/runner.py wrap each Lean subprocess in `bash ../../lean-slot.sh nice -n 10` and
set LEAN_SLOT_TAG=io-phfe. The wrapper SHA256 must remain
ff64d8d5b6baf4e7b1c15172a7faeb70246f22c6acf76134bbdb70c017f41f1a.
Do NOT wrap the entire Python runner in lean-slot: each subprocess already takes its slot;
an outer wrapper would hold the slot while its child waits. No parallel runner invocation.

The new scripts have separate provenance. They preserve/import the pinned builders and
request adapter as reviewed libraries; they do not mutate them. Historical BB1/default
paths and fixed 59-module defaults in archived build_seals.main/build_controls.main are
not invoked. The supported mkseals_ab/coE entry points configure those builder functions
and obtain actual Names from the completed collector.

## Step 1 — snapshot and source binding

Set these once in the root shell (TREE is root's existing completed bootstrap object tree):

```sh
WT=/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange
PREP=/private/tmp/io-phfe-drafts/rule10-prep
EV="$WT/evidence/rule10-m0"
TOOLS="$WT/evidence/preparation/tools"
SCR=.lake/io-phfe-rule10
```

Text-only preparation, no Lean or Git processes:

```sh
python3 -I "$PREP/prepare.py" --root "$WT" --out "$EV"
python3 -I "$PREP/reader_catalog.py" "$EV" "$EV/ReaderCatalog.lean"
```

Only after M0 source is committed, root runs this READ-ONLY Git comparison. It requires
all owned modules to equal BOTH snapshot bytes and that exact HEAD; it refuses source or
module-list drift. This is not a Git mutation and not a passing Lean audit:

```sh
python3 -I "$PREP/bind_head.py" "$EV"
```

Store the compiled source-to-HEAD build summary separately, as required by the brief.
These generators cannot establish whether the object tree contains stale owner oleans.
Root must finish bootstrap at the source-bound HEAD before collection.

## Step 2 — native collection and reader validation (one slot per probe)

Copy only generated audit probes into ignored scratch, never library source:

```sh
mkdir -p "$WT/$SCR"
cp "$EV/Collect.lean" "$WT/$SCR/Collect.lean"
cp "$EV/ReaderCatalog.lean" "$WT/$SCR/ReaderCatalog.lean"
printf '%s\n' "$SCR/Collect" "$SCR/ReaderCatalog" > "$EV/collector-order.txt"
env LAKE_PACKAGES="$WT/.lake/packages" python3 -I "$TOOLS/seal/runner_full.py" \
  "$WT" "$EV/collector-order.txt" "$TREE" "$EV/collector-run"
```

The canonical runner takes the pinned slot separately for each `lean -DmaxErrors=0` call,
sets LEAN_SLOT_TAG, and records both error diagnostic forms. It does not write to TREE.
Use fresh log directories, never append a second attempt into prior results.jsonl.

ReaderCatalog logs one PHFE_READER row per requested def/abbrev, then requested/verified
counts. Its assertion rejects a missing/ambiguous target or reader, non-theorem reader,
or a reader whose actual type omits the actual target. It also logs every native owned
definition, including generated projections and proof/instance flags. A source-name
candidate is not a verified reader until this probe succeeds.

If a candidate is wrong, choose the actual published reader from the candidate list,
update the coverage row transparently, regenerate ReaderCatalog and rerun; retain the
failed attempt. Do not silently waive an ordinary algorithm or invent a reader.

## Step 3 — whole-file A/B strict and coe seals

Use the exact collector log name emitted by the runner (`.lake` in SCR is retained):

```sh
COLLECTOR="$EV/collector-run/mods/.lake_io-phfe-rule10_Collect.log"
READERS="$EV/collector-run/mods/.lake_io-phfe-rule10_ReaderCatalog.log"
python3 -I "$PREP/make_seals.py" --snapshot "$EV" --tools "$TOOLS" \
  --collector-log "$COLLECTOR" --out "$EV/seals" --scratch-rel "$SCR/seals"
```

This invokes only the pinned Python generators and their read-only `git show FULL_HEAD`.
It checks frozen bytes/tool hashes and complete CAT/ROOT/CLOSURE/MODULE counts first.

Variants, with NO extra definition exclusions:

| Variant | Canonical generator | SEAL_EVAL | Exact notation exclusions |
|---|---|---:|---|
| strict-A | mkseals_ab.py | 0 | Complexity.PolyExpr.eval |
| strict-B | mkseals_ab.py | 1 | none |
| coe-A | mkseals_coe.py | 0 | eval and FinDist.instCoeFunForallReal |
| coe-B | mkseals_coe.py | 1 | FinDist.instCoeFunForallReal |

coe-A is canonical for the brief. All four run sequentially. SEAL_CHUNK=200 prevents
oversized harness commands; source-byte mapping, actual Name components, instance mask,
install and EOF verification remain the unchanged suite's behavior.

```sh
for V in strict-A strict-B coe-A coe-B; do
  env LAKE_PACKAGES="$WT/.lake/packages" python3 -I "$TOOLS/seal/runner_full.py" \
    "$WT" "$EV/seals/$V/order.txt" "$TREE" "$EV/seals/$V/run"
  python3 -I "$PREP/check_records.py" --records "$EV/seals/$V" \
    --run "$EV/seals/$V/run" --tools "$TOOLS" --out "$EV/seals/$V/record-check.json"
done
```

Also run canonical sealsum.py against canonical touched.py output for failing-declaration
mapping. The supplemental check_records requires requested=verified at install AND EOF,
actual component checks and the scoped instance-unfold mask verification, not just marker
presence. It checks every chunk and both error forms. A failed harness is never a source
finding or a sensitivity success.

## Step 4 — paired negative/positive controls

After native reader validation and seal preparation, one pair is generated per written
public def/abbrev for each variant. Both sides use the FULL type of the actual published
reader (`type_of% (@Reader)`) so the control statement does not itself unfold a foreign
type family. The positive applies @Reader. The negative uses reflexivity after binding
all arguments. Unsealed baseline: BOTH pass. Sealed: negative exactly one error in its
proof region, positive zero; successful install/EOF/component/mask records required.

```sh
for V in strict-A strict-B coe-A coe-B; do
  python3 -I "$PREP/generate_controls.py" --snapshot "$EV" --tools "$TOOLS" \
    --collector-log "$COLLECTOR" --reader-log "$READERS" --seal-dir "$EV/seals/$V" \
    --variant "$V" --out "$EV/controls/$V" --scratch "$WT/$SCR/controls/$V"
  env LAKE_PACKAGES="$WT/.lake/packages" python3 -I "$TOOLS/seal/runner_full.py" \
    "$WT" "$EV/controls/$V/controls-order.txt" "$TREE" "$EV/controls/$V/run"
  python3 -I "$TOOLS/seal/review/ctlcheck2.py" "$EV/controls/$V/controls-plan.json" \
    "$EV/controls/$V/run" "$EV/controls/$V/canonical-result.json"
  python3 -I "$PREP/check_records.py" --controls \
    --records "$EV/controls/$V/controls-plan.json" --run "$EV/controls/$V/run" \
    --tools "$TOOLS" --out "$EV/controls/$V/record-check.json"
done
```

For ordinary defs the chosen owner seal is the smallest actual request set containing the
target, as in mkctl_bb1s. Pairs sharing that seal are batched into one file to avoid
thousands of redundant Lean startups; every negative and positive has its own source span. Missing consumer coverage fails closed. A public abbrev absent
from canonical ordinary requests is retained in a separately labelled forced-opacity
alias diagnostic group per defining module, not an ordinary seal pass. Its status remains explicit in
coverage.json. No actual algorithm def is treated as a type alias by name heuristic.

Control sensitivity is UNMEASURED until the unsealed/sealed runs. If a negative fails
unsealed, refine its proof to the owner's actual unfolding route and retain both attempts.
If it passes sealed, investigate proof irrelevance, projection reduction or an insensitive
reader equation. No automatic waiver exists. The 40 instances remain in the native census
and canonical instance mask; their ordinary reader exemption is explicit, not a missing
algorithm control. Generated record projections/eliminators are separately classified.

## Explicit unfold and generated-equation scan

snapshot/static-explicit-scan.json is TEXT-ONLY: the current snapshot has 8 tactic items,
4 owned-definition candidates, 4 unresolved, and zero generated-equation candidates.
It is not a native foreign-reader PASS. The required canonical scan1_g40.py/scan2.py must
still run at frozen HEAD with SCAN_IMPORTS from all owned module roots. scan1 itself is
text-only and writes a native kind probe; root runs that probe through runner_full under
the pinned slot, then runs scan2 against its log. Use canonical touched.py spans.

Explicit `unfold name` is not a reliable negative opacity control: Lean 4.25
Lean/Meta/Tactic/Unfold.lean:21-25 uses the generated unfolding theorem or deltaExpand;
Lean/Meta/Tactic/Delta.lean:17-24 expands any hasValue constant, with no irreducibility
check. Such explicit body reads are caught by the separate policy scan, including foreign
Core/Mathlib and generated .eq_N/.eq_def/.eq_unfold reads. This was source inspection only,
not a native experiment or passing result.

## Completion requirements

Prepared coverage currently has requested_pairs=387, executed_pairs=0, verified_pairs=0.
There are no verified install/EOF records yet. Never turn candidate/prepared fields into
verified ones manually. Require all frozen modules, native names/readers, ordinary paired
controls, exact alias/proof-irrelevance dispositions, all four seals, both control checkers,
static/native explicit scan and generated-equation review before reporting Rule10 PASS.
M0 substantive theorem admissions remain a separate statement-stage census.

Exact canonical explicit-scan commands, after HEAD binding (root only):

```sh
python3 -I "$PREP/make_explicit_scan.py" --snapshot "$EV" --tools "$TOOLS" \
  --out "$EV/explicit" --scratch "$WT/$SCR/explicit"
env LAKE_PACKAGES="$WT/.lake/packages" python3 -I "$TOOLS/seal/runner_full.py" \
  "$WT" "$EV/explicit/explicit-order.txt" "$TREE" "$EV/explicit/run"
python3 -I "$TOOLS/seal/scan2.py" "$EV/explicit/explicit-items.json" \
  "$EV/explicit/run/mods/.lake_io-phfe-rule10_explicit_ExplicitKinds.log" \
  "$EV/explicit/result.json"
```

The touched.json made here is also the canonical input for sealsum.py:

```sh
for V in strict-A strict-B coe-A coe-B; do
  python3 -I "$TOOLS/seal/review/sealsum.py" "$EV/seals/$V" "$EV/seals/$V/run" \
    "$EV/explicit/touched.json" "$EV/seals/$V/source-summary.tsv"
done
```

Inspect all native scan classifications, especially unresolved and generated-equation
rows. An empty grep or scanner rc0 alone is not an explicit-reader pass.
