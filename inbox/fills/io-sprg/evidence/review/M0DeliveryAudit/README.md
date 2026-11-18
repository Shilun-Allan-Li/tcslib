# M0 delivery finalizer audit — read only

No audited script was run. No Lean, Lake, cache, git command, source/evidence edit,
or spawn was performed. Only this temporary note was written. Findings are in
findings.json with source lines and minimal repairs; snapshot.json binds the
inspected tool bytes and actual evidence schemas.

The definite runtime blocker is the lowercase reductionTargets extraction name.
Two concrete status/binding claims need adjustment after the planned empty M0
marker: retained no-freeze prose, and build/summary.txt's unchanged d286 HEAD line.
The endpoint-only PDF check is a narrower coverage gap, not a detected PDF.

The following schemas/paths match their current producers:

- axiom summary keys stored_constants/public_types/root_nonstandard/
  direct_sorry_constants/transitive_sorry_constants; counts1036/948/0/146/265;
- print-comparison keys all_match_current_graph and printed_public_theorems511;
- explicit-classified.summary has items21 and foreign_items0;
- request-counts.json is a LIST of88 per-owner records with variant/requested;
  its totals exactly match current manifests:23333/23350/23315/23332 for
  strict-A/strict-B/coe-A/coe-B. Do not substitute request-counts-final.json,
  which is an older four-summary file with requested_total,14 fewer per variant;
- source inventory's old TSV has146 unique Lean_name records and milestone,
  file_line, owner_proof_sketch columns. Both input owner lists contain22 files;
- ctlcheck2 produces an all_ok object; the pilot has that exact schema;
- current plans contain88 seals plus96 control probes, matching planned184.

Missing complete-runtime/ctlcheck/seals-summary files are expected queue and
summarize outputs, not evidence of a finalizer schema defect. Before finalization,
regenerate complete-runtime-check.json with the latest dynamic_counts.py AND
--environment-tree for the job olean tree: the current progress/current snapshots
lack environment_sha256, while the latest producer adds it and finalizer requires
an exact non-null environment binding. Do not copy an older progress snapshot to
the final filename. Run summarize to create all four ctlchecks and strict TSVs.
The finalizer should remain gated until every required current artifact exists.

The packager's manifest/replay code has no additional confirmed schema error on
these inputs. --zip must be supplied with an output outside the payload directory
for the required ZIP; placing the ZIP inside dest after manifest creation would
add an unlisted path. The report path is resolved from process cwd, so use the
absolute finalized evidence/REPORT.md path when invoking from another worktree.
Its base/head bundle branch check and empty-marker format-patch/am options agree
with the existing successful empty-marker replay evidence. Final execution and
exact replay remain root-owned and were not repeated by this audit.

Current evidence has no symlinks/PDFs, about1.112GB across2508 files at inspection;
largest file is33,642,327 bytes. These are transient packaging-input measurements,
not claims about the eventual ZIP, exchange push, or final manifest.
