# Hash-sign Rule-10 preparation tools

These tools prepare sources and manifests. They do not run Lean or Lake.
All generated Lean probes must be checked separately, one module per
`scripts/lean_check_tree.sh` invocation, against the appropriate phase's olean
tree. Base and final collection must each use oleans of that phase's sources.

Owners are auto-discovered from the selected immutable Git revision: the owned
`HashAndSign` facade plus every `.lean` file under its helper directory. At the
base, working helper sources that do not yet exist in that revision are recorded
as absent, rather than assigned fabricated base checks. Final preparation fails
if a working helper source was omitted from the selected committed revision.

The retained collector and seal instrumenter came from the base repository's
`briefs/pass-shelat-ch5-8/fills/dl-folds/final-r1/review-evidence.zip`.
`extraction-provenance.json` records the archive and entry hashes.
`adaptation-provenance.json` records the precise-import scan adaptation and the
new `prepare.py` adapter. The original instrumenter, its component-identity and
instance-mask adapter, and the legacy payload dependency are all delivered.

## Phase preparation

For each phase, select a distinct final evidence directory, such as
`evidence/rule10/base` or `evidence/rule10/final`. The examples below use
placeholder paths; supply absolute paths to the delivered tool and checkout.
Use the exact committed revision for `REV`. The seal builder reads source bytes
from Git, so commit final sources locally before preparing final seals.

```sh
python3 -I TOOL/prepare.py collect --repo CHECKOUT --phase base --rev REV --out OUTPUT
```

This creates `.lake/hash-sign-rule10/base/Collect.lean` in the checkout and a
verbatim evidence copy. For final, use `--phase final`; all subsequent commands
use that same phase, revision and output directory.

Check the returned probe module with `scripts/lean_check_tree.sh`, retaining the
complete raw log from the start at its final evidence path. It prints:

- `CLOSURE` records derived from the loaded environment's actual imports;
- a `CAT` record for every TCSlib definition in the environment;
- `ROOT` records for every stored constant of each owner, including private and
  generated constants, with foreign type and value references;
- `AXIOMS` for every such stored constant;
- explicit `#print axioms` output for `hashAndSign_oneTimeSecure`.

Then prepare seals from that successful collector log:

```sh
python3 -I TOOL/prepare.py seals --repo CHECKOUT --phase base --rev REV --out OUTPUT --collector-log COLLECTOR_LOG
```

The default A seal exempts `PolyExpr.eval`; the B seal includes it. All other
ordinary semireducible definitions and generated matchers in each owner's full
TCSlib import closure are covered, including definition-instances. Reducible
abbreviations remain explicitly recorded exclusions. Requests use actual name
components, verified home modules and metadata; installation and EOF verification
are retained. Large request sets are split into commands of 500 requests.

The per-variant `manifest.json` files list the probe modules to check. Preserve
every generated `.lean.txt`, per-probe JSON, and the complete raw check logs.
Attribute every Lean error to its original declaration using the recorded
`source_to_probe_lines` mapping. Compare base and final failing declarations.

## Paired controls

```sh
python3 -I TOOL/prepare.py controls --repo CHECKOUT --phase base --rev REV --out OUTPUT
```

Each target chooses the smallest complete owner request record that covers it
to obtain verified constant identity and home metadata. By default the control
installs only that target's singleton request; `--control-mode whole` instead
installs the complete owner set. The full A/B source seals separately verify
installation and EOF persistence for every closure request. The baseline
`CostBoundedBy` pair used the complete A set; remaining baseline pairs use
singleton sets, as recorded in `controls-workflow-switch.json`.
The probes import that owner's direct imports from the selected immutable Git
revision, rather than the owner module itself. This loads exactly its foreign
closure and allows later proof edits without changing baseline control imports.
Controls cover `padFin`, `NUPPT.inArg`, `OracleComp.CostBoundedBy`,
`PolyExpr.eval` in B, and the new helpers' `collisionKey` and `indexWord` when
those are foreign to a consumer. `OneQuery` contains no new definitions;
`CostBoundedBy` tests the foreign predicate it consumes. `OneQuerySampling`
and `CodecReaders` likewise introduce only theorems, without a new definition.

Each unsealed probe contains a body-reading negative and published-reader
positive and must pass. The matching sealed probe must report exactly one Lean
error, belonging to `HashSignSensitivity.negative`; its reader positive must
have no error. `controls-plan.json` records exact lines and expectations. The
checker script's expected nonzero exit and missing olean for a negative are
retained as raw evidence. These failures are sensitivity evidence, not failed
proof-module checks.

`run_controls.py --out OUTPUT --repo CHECKOUT --prefix UNIQUE_LABEL` runs the
active plan serially through the retained `check_module.py` and `run_probe.py`
wrappers, checking these exact expectations. `run_probe.py` also checks one
ordinary prepared probe, records memory/times/hashes, and attributes seal
failures using its `--record` source-line map. Its results append to
`OUTPUT/results.jsonl`; original check logs stay in `evidence/logs/`.

## Explicit-unfold scan

```sh
python3 -I TOOL/prepare.py scan --repo CHECKOUT --phase final --rev REV --out OUTPUT
```

This records declaration changes against the issue base and runs the retained
source lexer. Its native name-kind probe imports precisely the scanned owners.
Check `.lake/hash-sign-rule10/final/ExplicitKinds` through the required module
script, then classify the complete raw probe log:

```sh
python3 -I TOOL/scan2.py OUTPUT/explicit-items.json NATIVE_KINDS_LOG OUTPUT/explicit-final.json
```

The scan classifies both foreign TCSlib definitions and foreign Core/Mathlib
definitions passed explicitly to the covered tactics, including generated
equation lemmas. Review every `LOCAL_OR_UNRESOLVED` item as well as every foreign
item. The seal covers implicit definitional reads; neither check substitutes for
the other.

## Delivery completeness

Retain the tools, provenance, collector/axiom sources, seal sources, controls,
requests, manifests, scan records, every raw log, and all results JSONL files.
Include them in the delivery manifest and verify exact path equality with that
manifest before packaging. No source or check preparation performed by this
tool establishes that a check passed.
