# Keyed-table fill, round 2 — final

Both frozen targets are proved with C = 64, without admitted dependencies.
The required downstream replay passed. See final-downstream-summary.json, downstream-all-importers.txt, downstream-full-order.txt and each per-module log. 887 additional modules were compiled fresh in this fill's own tree.

- Repository: Shilun-Allan-Li/tcslib.
- Base fetched read-only: `7342f98b58704d6c25faf668ed1a64ea0b27c4af` (ram/readers-2, PR #375).
- Rules and brief: `e40383d88d79e23026c95e20608ee8827d45e59b`, including COMMON's tier 2 addendum.
- Local branch: codex/fill-ram-key-table-r2, never rebased or pushed.
- Source commit: `7ac230a14e4633f074a5aa8d94201ed7eedf6ecc`.
- Owned source SHA256: `ca4094170725cea75a1c55bf7494b5f1e3778bcf392b27bbca9b05c011a6e545`.
- Owned file: `TCSlib/Complexity/TuringMachine/Build/KeyTable.lean`; 3574 lines.

The original exchange README and bundle matched SHA256SUMS; the recorded bundle SHA256 is
14de9a4a1ba6ca97c0508bacb0fbef22843cf29341c63a59fd34b5844abef26f. See
dispatch-input-integrity.log. Round 1 changed no library source and requested the three layout
readers now published in PR #375; this round starts from the replacement base above.

## Targets and verification

| Target | Result | Axioms |
|---|---|---|
| Turing.exists_keyLookupTM | Proved, statement byte-identical | propext, Classical.choice, Quot.sound |
| Turing.exists_keyAssignTM | Proved, statement byte-identical | propext, Classical.choice, Quot.sound |

No sorryAx is reachable, so each target's admitted-declaration list is empty. No RecordTable
admission or WordArith admission is cited. FinalMetadata.lean prints both targets' axioms and
calls collectAxioms on all 736 explicit/generated private constants and headline roots,
rejecting any nonstandard axiom. AUDITED-CONSTANTS.txt lists every root.

| Check | Exit | Evidence |
|---|---|---|
| Native owner elaboration | 0 | keytable-179-final-native; fresh nonempty olean, no warnings |
| Axiom/dependency census | 0 | final-metadata-04; both targets and 736 roots |
| Foreign-definition seal | 0 | final-seal-09; all 48 reached heads irreducible |
| Frozen source surface | 0 | final-source-freeze.json; original definitions and both statements byte-identical |
| git diff --check | 0 | Checked before source commit and packaging |
| Style lint | 1 | Exactly one finding: file size; explicit tier 2 size exception applies |

seal-09-source.json binds the sealed copy to the exact delivered source hash. All developmental
failed checks remain in the evidence; the final success labels above supersede them. The
required downstream validation status is stated explicitly above.

## Construction and endpoint

One private marker contract transformer opens the payload delimiter, places a published row,
and restores the marker. It is shared by comparisons and both copy directions, including empty
words. The finite search controller uses phaseHostTM and Contract.inPhase with the catalog's
compare, copy, skip, scan and rewind rows. Its only raw leaf performs a fixed one-cell tape
action, absent from the catalog; that leaf also restores and appends markers.

Lookup keeps the first matching value or scans zeros into the original register interval.
Assignment updates every matching value at its original width. If no key matched, the same
field-append implementation writes the marked key and value into the blank tail, each in
3 times its payload width plus 14 steps, and rewinds. Full-layout and SameOutside facts give
exactly keyTableWrite at the endpoint. Entry costs telescope, and both full runs use C = 64.
The shared final anchor cannot be revisited; the model's one-cell-per-step head bound supplies
the radius. All other heads and the input/output frame are restored.

## Scope, readers, reuse and size

Only the owned library file is in the patch. The added existing Build/InputRewind import
supplies Cfg.mapState_mapState. No new public declaration, reader, simp attribute, axiom or
admission was added. No private rt_* declaration is used. Both targets' sketches describe the
actual proofs, and every nontrivial helper carries its local proof sketch.

INVENTORY.md lists all 175 named private declarations, roles and actual referenced
interfaces. FOREIGN-READERS.md lists all 48 foreign definition heads and their public
reading interfaces. The import-closure searches and interfaces used before the helper families:

- Marker and control: Catalog's compare/copy contracts, Contract.seq/inPhase, phaseHostTM run
  theorems, StateRenaming/CfgFacts field readers and InputRewind's state-map composition.
- Traversal: skipTM_contract, compareTM_contract, copyTM_contract, scanTM_contract and
  tableRewindTM_run_ofCfg. Segment/SafeSegment/RoundContract were inspected; the shared phase
  placement and exact run concatenation suffice here.
- Layout: PR #375's tableFields_eq, tableWF_iff, tableAt_iff, plus TableAt.recordAt_take,
  fieldOffset_length, tableOffset_eq/length, fieldsTape_field/cons_shift/of_neg/of_length_le
  and joinFields equations. One private append decomposition, proved from public tape equations,
  is reused for equal-width replacement and tail growth; no private RecordTable proof was copied.
- Frames: Cfg.sameOutside_iff and Cfg.SameOutside.keep_word preserve stored query, register
  and scratch words. One complete table write absorbs earlier in-table updates.
- Mathematical results: List.find?/drop equations for first-match lookup; List.any/map/append
  equations for all-match assignment. The flagged suffix recurrence agrees with keyAssign.
- Factoring: the marked-write boundary proof was generalized and its former equal-width
  proof became a corollary. Header preparation, both operations' entry scan, all three adapted
  copies, all field skips, and both new-field appends use common helpers. Dead raw-contract
  scaffolding was removed. No copied proved variant is being silently delivered.

Suggested shared-layer promotion at landing: the marker contract transformer and its delimiter
facts, the full-layout append/replace helpers, and the framed table-rewind contract. These are
private as required by the owned-file brief. The explicit tier 2 rule says to continue past
1,500 lines and report the size; the maintainer splits the 3574-line file at
landing. This is the sole style-lint finding, not an unfinished proof.

Patch against the fixed base:

```text
.../Complexity/TuringMachine/Build/KeyTable.lean   | 3425 +++++++++++++++++++-
 1 file changed, 3404 insertions(+), 21 deletions(-)
```

Thirty unrelated dirty blueprint files predated this work and are preserved, unstaged and
excluded. Local proof commits were never pushed. Exchange delivery touches only the named zip.

## Environment and process record

Native macOS, pinned Lean v4.25.0. Initial preflight recorded 12 CPUs, 18 GiB physical RAM,
59% available memory by memory_pressure and about 111 GiB free disk. Native sysctl/vm_stat and
time -l replace unavailable Linux diagnostics. Package URLs/revisions match lake-manifest.json;
.lake/packages is the authorized pin-verified symlink to the existing cache. No lake build was
run, no foreign fill olean was used, and no dependency tree was copied or merged.

The initial 38-module base closure and the added InputRewind module were compiled fresh in
.lake/fill-ram-key-table-r2-oleans. Final downstream prerequisites use the same tree and base
sources. All 360 Mathlib roots needed by the full facade closure were already present in the
pin-verified cache; no unfiltered cache fetch was run. Downstream manifests record exact order
and provenance. Every check uses the campaign leanelab wrapper, nice -n10, -j4 and
TCSLIB_LEAN_SLOTS=3, plus a machine-wide executable count and an OS per-fill fcntl lock. Old
oleans are deleted before compiling and a fresh nonempty output is required. Waits and exit
codes are recorded in the logs.

Actual process deviation: checks55/56 overlapped for about 130 seconds after a running session
was mistaken for a terminal result. Two own Lean processes ran concurrently; the recorded
machine-wide count was two. Both failed, both products were discarded, and no olean remained.
They were never used as evidence. A per-fill fcntl lock was added; fresh serial check57 and all
subsequent successes supersede them. The overlap/resource recheck logs disclose this deviation.
It did not end the fill, as the environment addendum requires. No further own-process overlap
occurred. Machine-wide waits are in lean-processes.log.

Delivery uses a separate sparse exchange clone backed by existing local Git objects. The shared
exchange checkout, including other fills' pending files, is untouched. Pull --rebase precedes
each exchange push; no force push and no pull request.

## Archive

REPORT.md, INVENTORY.md, FOREIGN-READERS.md, AUDITED-CONSTANTS.txt, the owned source at its normal
path, its patch against the base, all round-2 logs/probes and the runtime scripts. MANIFEST.sha256
covers every file except itself. No compiled objects or unrelated workspace files are included.
