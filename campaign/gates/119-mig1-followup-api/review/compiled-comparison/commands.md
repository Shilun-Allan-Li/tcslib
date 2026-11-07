# Actual managed invocations

All shell commands began by sourcing the scratch environment. Probe inputs were fully
reviewed before the following sequential invocations:

```sh
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
set -e
python3 -I campaign/gates/119-mig1-followup-api/review/compiled-comparison/run.py base
python3 -I campaign/gates/119-mig1-followup-api/review/compiled-comparison/run.py head
```

Exact managed-wrapper argument arrays, temporary input paths, input/output hashes, times and
exit statuses are in `Inventory-{base,head}-request.json` and `Inventory-{base,head}-run.json`.
Both inputs are exact copies of `Inventory.lean.txt`. They import all five modules and add no
public declaration or compiled output. No delivered script was run and no native rerun was
performed after the two completed metadata probes.

`prepare.py` captured read-only Git baseline source, current source and olean pins.
`source_reconcile.py` independently checked the source/API delta using the existing trusted
balanced header reader as a pure function. `analyze.py` reconciled all native populations,
including exact shared types/attributes and every axiom closure. All ran with `python3 -I`.

After native validation, `archive_logs.py` deterministically compressed and byte-verified the
complete raw payloads before replacing the flat `.out` files. `archive_utf8.py` then encoded
and independently verified the full archives as UTF-8 Base64. `analyze.py` was rerun only as an
offline parser against those same byte-verified outputs; this was not a new Lean execution.
Every actual native attempt and all probe inputs are retained, without filtering or caps.
