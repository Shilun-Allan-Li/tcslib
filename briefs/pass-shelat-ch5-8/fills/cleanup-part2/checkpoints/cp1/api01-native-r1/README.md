# CP1 API-01: checked local follow-up

**API-01 is corrected on the isolated local review branch**, at
`8c047b8bcd3a2793795a02afd6d2d955c80e1806`. The immutable CP1 and review-r1 remain unchanged; this is a
separate maintainer follow-up. The worker's continuing source has not incorporated
this local commit by implication.

The patch removes the new whole-machine equality alias and replaces its three
consumers with the existing `NUPPT.output_ofPolyTimeUniform` contract. Four files,
three inserted and ten removed lines; no existing theorem header, algorithm,
bound, assumption or admission changes. Seven preceding worker patches retain
their author attribution. The branch is local only: no source push or PR.

The fresh serial run passed all **101 local prerequisite/consumer modules** plus
a Mathlib cache import probe, using `scripts/lean_check_tree.sh`, one module per
invocation and one native process at a time. A separate final probe printed the
actual axiom sets of the three repaired proofs and three machine API constants.
All six contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
All 101 source/object identities and direct prerequisite hashes reconcile.
The run used no TCSlib object copy/reuse and left the old S2 object tree intact.

Preflight: macOS12 logical CPUs /18GiB physical memory, native memory-pressure
query73% free, APFS408,420,340KiB available on clone/scratch/temp volumes;
11 present packages match manifest URL/revision, four doc-only packages absent,
zero empty package oleans. The same-chat pinned package cache was already
populated; all66 direct Mathlib roots and the required external object closure
were present, and the native cache probe passed. No new cache fetch was needed.
Peak recorded per-module RSS was 2295775232 bytes. Every attempt has an exclusive
log path with START/END/return code/source/prerequisite/log hashes; no attempt
failed or was overwritten. Full preflight and raw evidence are in the ZIP.

The source pins in the native run describe the review head plus the exact repair
diff before it was committed. The final commit changes no checked source byte;
repair.json binds that commit to the patch and run. Native tools are the own
reviewed runners, never incoming checkpoint scripts.

**Limits:** these are ordinary unsealed checks of this bounded API follow-up,
not the entire cleanup affected/downstream/root/Checks replay or fresh full
seal/C3/control/census evidence. Three workflow majors and the ledger minor
remain, alongside unfinished inherited-read repair and the inherited instance
coverage question. This does not accept CP1 or authorize a merge.

**Not yet clear to merge — the local API repair is checked; the remaining partial fill and final evidence are open.**
