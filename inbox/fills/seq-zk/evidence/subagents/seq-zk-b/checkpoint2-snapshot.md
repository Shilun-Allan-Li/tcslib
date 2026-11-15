# Closed seq-zk-b evidence snapshot for checkpoint 2

Snapshot source: e978a28274fdeb545e622ae28747221088352512. checkpoint2-source-hashes.tsv
records that commit's helper hashes, independently of later working-source additions.
checkpoint2-closed-files.tsv lists SHA256 and repository-relative paths of every closed
file under this sub-agent evidence directory at snapshot time, except that manifest itself.
All subprocesses are complete; no running log is listed. The listed bytes are now frozen.
Future work writes new evidence filenames rather than mutating these captured files.

checkpoint2-evidence-scope.tsv marks new SuffixMachine/canonical Eq-reader evidence as
post_cp2_future. Those additions are outside the e978 source snapshot. Earlier searches,
success/failure logs, probes, and summaries are retained, including all failed attempts.
The snapshot metadata files are marked snapshot_metadata. No raw evidence is omitted.
