# ext-nosrc Rule 10 tools

The preparation agent did not run Lean. Root controls all Lean execution and the
selected, already bootstrapped olean tree. The Python preparation and driver
source files are delivered with the probes and raw logs they generate.

Run from the isolated fill checkout, with Python isolation enabled:

```sh
python3 -I evidence/tools/run_rule10.py census base
python3 -I evidence/tools/prepare_rule10.py seals base --census-log evidence/rule10/base/logs/Census.log
python3 -I evidence/tools/run_rule10.py seals base
```

The base preparation already exists. The census driver first checks an exact
`git show eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9:.../Extraction.lean`
snapshot under a distinct probe module, then imports that snapshot for its
environment census and every-stored-constant axiom records. It therefore does
not mistake a final owned-module olean for a base olean.

After freezing final sources and checking all final owned modules:

```sh
python3 -I evidence/tools/prepare_rule10.py init final
python3 -I evidence/tools/run_rule10.py census final
python3 -I evidence/tools/prepare_rule10.py seals final --census-log evidence/rule10/final/logs/Census.log
python3 -I evidence/tools/run_rule10.py seals final
```

Pass `--tree /absolute/path` to the driver if root uses a different olean tree.
The default is the checkout's `.lake/tcslib-check-oleans`. The driver calls
`scripts/lean_check_tree.sh` once per module and records native timing and RSS;
it does not run Lake or a direct Lean command. It does not impose timeouts.
It rejects existing logs/results rather than overwriting earlier attempts. A
retry should use a new evidence directory/module name or preserve the prior
attempt first and explicitly regenerate its prepared metadata.

The source/import hashes, complete TCSlib import closures, raw owned-source
snapshots, census collector source, census log, census results, all constant
records, all-stored axiom records, validated abbreviation exclusions, exact
request manifests, complete seal/control sources, line maps, install/EOF
name/home records, raw logs, per-probe results and `*-results.jsonl` must all be
retained and included in the final evidence manifest.

Seal A exempts `Complexity.PolyExpr.eval`; seal B includes it. Every other
request is shared. All imported TCSlib definition constants whose native home
lies in the source's complete import closure are candidates, including
instances, generated matchers and generated projection definitions. Only
constants whose definition hints are actually `abbrev` and whose current
reducibility is validated as reducible are excluded under the abbreviation
notation rule; matchers remain candidates even if marked reducible. No unsafe
reducibility override is used. Printed-name ambiguity, wrong module ownership,
nondefinition requests, inactive seals or count mismatches fail closed.

Original source bytes are preserved by insertion-only instrumentation. The
request seal is installed after the imports and before the first original
command and reverified at EOF, so namespaces, anonymous commands, instances and
generated declarations are included in the whole-file re-elaboration. A new
helper has no base predecessor: base covers Extraction only, final covers all
three owned/new modules.

Unsealed `rfl` controls for `padFin`, `runAtL` and `PolyExpr.eval .var` must pass.
Their sealed variants must fail exactly once, except the eval A variant which
has no eval request and must pass. Reader-based controls use `padFin_apply`,
`NUPPT.runAtL_eq` and `PolyExpr.eval_var` and must pass under both variants.
These controls validate ordinary body reads and the eval distinction; they do
not themselves provide a separate matcher-only negative control.

The driver rejects errors in instrumentation, missing/duplicate install or EOF
completion markers, a mismatch between the actual native name/home sequence
and requests, changed sources, and inconsistent native statuses/object
freshness. Source failures in valid whole-file seals are collected for every
module; every failing declaration must still be identified and compared with
the base by root. An explicit-unfold scan is separate from this harness.

Preparation tools were inspired by the environment census and byte-preserving
seal instrumentation of
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/{Collect.source.txt,build_seals.py}`,
and its `tool-inputs/request_payload_adapter.py` bounded-AST payload design.
Those files were read as working material. Their old fixed campaign pins,
51-module assumptions, skips and entrypoints are not executed by this tool.
