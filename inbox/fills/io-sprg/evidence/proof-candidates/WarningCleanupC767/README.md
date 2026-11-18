# Twelve Lean warning cleanups — NOT APPLIED / NOT COMPILED

These eight proof-body edits address the exact twelve non-sorry diagnostics in
the historical c767ee8 all-owner build: LPN1, Degree1, Correctness4 and Stretch6.
The four base source files were copied while their hashes still matched the
root-produced c767 sizes inventory. No implementation file was edited; no Lean,
Lake, Git, cache, source application or agent was run. The pure producer only
writes temp references, triage records and candidate diffs.

- warning-triage.tsv/json:all twelve exact file:line:column diagnostics, owner theorem,
  log hashes, proposed edit IDs and reasons.
- exact-replacements.json:eight unique before/after strings.
- *.proof-only.diff:one reviewed hunk set per file; no complete candidate module
  is supplied, to avoid overwriting root's new LPN reader or other later repairs.
- base-source/*.lean.txt:historical references only, never replacements for current source.
- source-bindings.json:old/proposed hashes and the unchanged-header/docstring checks.

W01 removes the specific hz simp argument marked unused; it retains Ne.symm hz.
W02 renames only the unused lambda binder d to _d, leaving the frozen theorem
binder/header unchanged. W03–W05 remove redundant simp arguments and only those
case equation labels no longer used. W06 replaces two unnecessary focused-sequence
operators with ordinary consecutive tactics. W07–W08 remove ring suffixes that the
actual logs say are unreachable/no-op because field_simp already solved the goal.

Root must merge the proof-only hunks into the NEW source; the old LPN whole-file
hash will differ once lpnNoise_law_cast is inserted. Do not copy any historical
base source over the current module. Exact before strings should still identify
the intended unaffected proof locations. Every patch still needs root's serial
compile, global frozen-header/prose guard, axiom checks and later opacity/seal checks.
No linter is disabled, no new assumption/theorem/import/attribute is proposed,
and no canonical-opacity success is claimed by this packet.

Historical M3 v1 READY was held after a focused lpnNoise-opacity failure. The
byte-preserved v1 packet is at ../M3CheckpointV1Historical-c767ee8. A new source,
reader, all-owner checks and separate READYv2 are required before publication.
