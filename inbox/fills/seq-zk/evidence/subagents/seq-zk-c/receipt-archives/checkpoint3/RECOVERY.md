# Exact checkpoint3 audit-file recovery

These two archived historical files were deterministically regenerated with the original
future-audit.py, whose bytes still match the CP3 receipt, in an isolated temporary tree.
No values were manually inferred, edited, or fabricated.

The reconstruction contains only the159 CP3 receipt paths, so the original tool scans
exactly48 preserved historical raw native logs. All15 source inputs are the immutable
CP3 checked-source snapshots, each verified against its own receipt SHA; in particular,
ContinuationProbability is the320-line a5922afe075adffb6349ba1801857125ac76ec158d4bca3faa8fc5289ee03d32
snapshot. The current354-line reader-fixed source was not used. The copied four later
changed JSON/JSONL paths are not audit scan inputs; the original tool overwrites both
outputs in the isolated tree. Its complete stdout, exact command and input hashes are
preserved in RECOVERY.log and PROVENANCE.json.

The regenerated outputs match the requested historical receipt hashes EXACTLY:
- future-audit-sources.json:7b34254d3d35a74796d68bf0f1c1e82edbce7850df1134ea67326f84f562cb33
- future-audit-checks.jsonl:b0c5536b01ddc22a5cb7fc781d7670e2586df7cda0ccf5ab806a49d1962c86f9

The171 current withV-fix receipt rows were verified byte-for-byte both before and after
recovery. The current audit JSON/JSONL and the current receipt manifest are unchanged.
Only this NEW receipt-archives/checkpoint3 path was written. The scratch reconstruction
is preserved locally at the path recorded in PROVENANCE.json; it is not a Lean run.
