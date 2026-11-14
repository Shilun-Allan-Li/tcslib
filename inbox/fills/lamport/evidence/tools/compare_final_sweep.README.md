# Final sweep and admission comparison

`compare_final_sweep.py` is source-only. It does not invoke Lean or Lake and never changes
raw sweep logs, result ledgers, source files, or earlier comparison attempts. It was prepared
and syntax-parsed before the final sweep; no final result is claimed by its preparation.

After the final sources are stable, use `prepare_sweep_order.py` to create a fresh final order
and its `source_sha256` audit. Run the complete order once through the sequential
`check_order.py` driver. Then run the comparison against that final attempt, for example:

```sh
python3 -I /private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence/tools/compare_final_sweep.py \
  --root /private/tmp/tcslib-lamport-01a1d88f/proof \
  --evidence /private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence \
  --order inputs/final-order.txt \
  --order-audit inputs/final-order-audit.json \
  --results logs/final-sweep/results.jsonl \
  --output logs/final-sweep-comparison-r1
```

Paths other than `--root` and `--evidence` may be absolute or relative to the evidence root.
The output must be a fresh directory inside evidence. Substitute the actual final phase
names for `final-order`, `final-sweep`, and the comparison attempt name. Default baseline
inputs are `logs/baseline-admissions.json` and `inputs/base-sorries.txt`.

Exit zero means all of the following hold:

- The structured baseline and issued text independently describe the same 22 declarations.
- The final order retains all 150 issued modules in their issued order.
- Every expected module occurs exactly once, in order, with result exit zero and its raw log.
- Raw START/END/EXIT markers agree with the result row, and each raw command names one
  `scripts/lean_check_tree.sh` call for the recorded module.
- No Lean error diagnostic or contradictory raw FAIL marker is present.
- Current source bytes match the separately prepared final-order hashes. Warnings are never
  resolved through a mismatched current file, including a temporarily restored issue-base
  Lamport file. If the runner records per-result `source_sha256`, those are checked too.
- The final warning declaration set has exactly 21 elements and differs from the 22-element
  baseline only by removal of `lamport_oneTimeSecure` from its owned Lamport module.

The tool recognizes ordinary and coded Lean error/warning diagnostics. It resolves each
`declaration uses 'sorry'` warning through the corresponding pinned final source, retaining
the declaration line, warning line/column, raw log line, and source hash. The declaration
spelling is preserved as written, including `_root_` names, to match the issued baseline.

The report separates omitted modules, unexpected modules, duplicate attempts, out-of-order
results, malformed JSONL rows, missing logs, nonzero process results, Lean errors, protocol
inconsistencies, unmapped warnings, duplicate warning occurrences, and admission-set changes.
It never silently chooses a last attempt from duplicate module results. Use a fresh complete
sweep attempt if a ledger contains retries or a partially failed run.

Every comparison attempt preserves exact copies and hashes of its order, source audit,
result ledger, baseline JSON, issued admission text, and comparison tool. Its outputs are:

- `report.json`: all coverage, status, raw-log fingerprints, and grouped issues;
- `admissions.json`: the final admission-warning/declaration census;
- `diagnostics.json`: every parsed Lean error and warning;
- `SUMMARY.txt`: concise pass/fail counts.

Raw compiler logs remain at their original final evidence paths. The comparison records
their hashes and does not overwrite, move, or trim them. The final evidence manifest must
include those raw logs as well as the comparison directory and tools.
