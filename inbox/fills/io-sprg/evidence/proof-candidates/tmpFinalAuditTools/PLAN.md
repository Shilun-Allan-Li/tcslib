# Dynamic final-audit tooling — read-only review

No scripts, Lean, Lake, Git or cache commands were executed. Only source reads/searches
and temporary notes occurred. Findings are byte-bound in source-bindings.json. Optional
coverage_contract.py.candidate is unrun, uncompiled proposal code, not a checked tool.
It introduces pure inventory/coverage functions only; root must integrate/review/test.

The current filesystem has a new Basic module while the checked-in M0 owner metadata
still has22 entries. Future added reduction modules require the same automatic path.
Do not replace22with23or27, or670/146with guessed new totals. The frozen M0 numbers
remain correct historical snapshot data. Keep its evidence/report intact; emit fresh
checkpoint evidence for later proofs and final delivery.

## 1. One immutable source inventory

Use the pinned Lean base5ed465f62e4ae0f93ded1a1ba49e807591b589eb, never M0 as the
owner-discovery base: unchanged-since-M0 newly added modules must remain audited.
Resolve HEAD once to a full commit and record base/head/tree plus source hashes.
The future root-run input is full `git diff --no-renames --name-status -z BASE HEAD --`.
Do not filter to already-known owner paths or read historical owners.txt as authority.
No Git command was run in this review.

Require each changed path to be a permitted Lean path. Owned means exact facade
TCSlib/Cryptography/Obfuscation.lean or a Lean file under the exact directory prefix
TCSlib/Cryptography/Obfuscation/. TCSlib.lean is a separately checked pure-export edit;
it is not an ordinary owner only because it adds no declarations. Any other changed
path fails. Reject deletions/type changes/renames unless separately reviewed; do not
silently drop them. --no-renames represents moves as deletion+addition, forcing review.
Use all statusA/M area paths, including Basic and every new nested reduction module.
Compare every worktree source byte to HEAD:PATH. Detect untracked area sources and
fail/record them as uncommitted rather than silently omitting intended new modules.

Write one inventory.json with base/head/tree, ordered owners, module/path/status/hash
rows, all changed paths, separate approved export rows, and a canonical digest. Derive
owners.txt/owner-paths.txt/files.txt from it as compatibility outputs; verify exact
set equality and uniqueness whenever loaded. Reuse the reviewed builder.header lexer
for import topology and reject cycles. No new fixed owner count is necessary.

prepare_static currently scans the tree and asserts22. Replace discovery only; retain
declaration/reader/classification logic and include inventory metadata in static-plan.
orchestrate must prepare BEFORE reading lists. Its current pre-refresh `mods/files`
variables would otherwise continue to omit Basic even after removing the22assert.
Each generation/run consumes one inventory head/digest; changing HEAD/source requires
a new snapshot or an explicit inventory mismatch failure, not partial in-place reuse.

## 2. Exact coverage before dynamic counts

At collector parsing reject duplicate CAT/MODULE/CLOSURE records before dictionaries
can overwrite them. Require CLOSURE.keys=MODULE.keys=expected owners, ROOT keys subset
owners, and for EACH owner len(ROOT rows)=stored count (including0stored facades).
Keep CAT-COUNT and exact Name uniqueness checks. Require the collector source's
imports/owners list and source/log hash to match this inventory and actual run.

For EACH of strict-A/strict-B/coe-A/coe-B require exactly one seal record per expected
owner, no duplicate/missing/extra owner or probe. Require those four variants exactly,
not just directories that happen to exist. Bind records/briefs to source/revision,
collector log, inventory digest and current environment. Keep current builders'
FULL conservative transitive import-closure rows, not term-only or changed-file-only
sealing. The module split changes ownership, not the closure eligibility predicate.

Derive control totals from the generated plans, not2*owners: controls use covering
owners, and theorem-only new modules may add no control group. Require paired sealed
and unsealed groups for each selected owner, unique control declarations/modules,
coverage.json unresolved empty, exact current eligible definition/reader target
coverage and all explicitly justified exclusions. No `NOT_REQUESTED` escape for an
otherwise eligible term-used ordinary definition. Preserve anonymous/generated
instance classification and the exact SizeOf/abbreviation/proof-instance exceptions.

Only AFTER these equalities derive seal_total=4*owner_count and control_total=sum
actual complete plan lengths. planned=seal_total+control_total. dynamic_counts currently
can call an undersized supplied matrix complete; replacing184withlen(report) alone
would remove the old accidental coverage guard. Require report keys equal the exact
validated plan keys and completed=planned with no NOT_RUN/FAIL_RECORDS. All canonical
coe-A/coe-B probes must have0rc/0both diagnostic forms/0substringerrors. Retain strict
failure attribution, four ctlcheck all_ok gates, all source/log/environment identities,
chunkpayload exact concatenation, Name/component identity, installed/already counts,
instance masks and INSTALL/EOF coverage. Never reduce a requested closure to save work.

Preserve serial root-only lean-slot.sh, LEAN_SLOT_TAG, exact pinned wrapper hash,
no-o runner semantics, memory/host gates, full environment hashing and reuse only when
source+log+environment all match. Additionally bind every expected owned olean/source
build record; a merely nonempty job olean tree is not evidence that all new owners built.

## 3. Current axioms, declarations and source inventory

CensusGraph has a literal22owner list and exact-home filter: facade import does not
cause Basic or new split roots to be inventoried. Generate its new checkpoint owner
list AND explicit imports from inventory. Compare per-module all-stored root counts
to the same current collector, including private/internal/generated constants. Parse
GRAPH-COUNT/ROOT-COUNT values and compare them to actual unique graph/root rows; the
current summary only checks that one marker exists. Keep complete dependency edges,
least-fixed-point propagation, actual axiom identities and all public kernel types.
Regenerate PrintAxioms from this full current public-theorem census; retain exact
printed-name-set AND axiom-set equality, without assuming511or any other count.

source_inventory must compute current lexical headers and remaining obligations.
Replace146/exactoldholes with remaining named holes SUBSET frozen named obligations,
reject every new sorry/admit/helper hole, and retain sketches/milestone classification.
Inspect all stripped-code tokens/declaration chunks, not only :=sorry stub syntax;
partial-body sorry must not vanish from the inventory. Compare to actual current kernel
sorryAx traces and account for anonymous/generated constants. Final stage requires
zero source holes and zero sorryAx in ALL required stored roots, not just headlines.
Use explicit TSV column schemas: current data[0] access crashes when obligations=[]
at final0holes. A header-only empty obligations TSV is the correct result.

Keep full frozen statement/header preservation separate from changing current counts:
read evidence/freeze/M0.txt (d10a560... currently matches cluster_audit's literal hash).
Reject CHANGED/REMOVED frozen statements. Additional theorem-only helpers need their
explicit approved ledger, overlap/reuse record, sketches, standard axioms and no added
algorithms/definitions. Do not relax cluster_audit's noADDED guard indiscriminately;
parameterize its expected permitted added theorem names, while preserving all others.
A moved frozen declaration needs an explicit owner relocation record and unchanged
name/type check; do not waive removal reports based on a module count alone.

## 4. Static/build/report/package consumers

static_refresh: all paths come from inventory; dynamic declaration counts must equal
its current parsed declaration set, with0unapproved changes/removals. For builds select
the latest exact-source successful record per expected owner in the checkpoint build
log and require exact owner-set equality, source/log hashes,0rc, both error forms and
no untriaged non-sorry warning. len(records)==owner_count is insufficient if duplicates
mask a missing module. Preserve1000lines/100columns, style/sk15/campaign baseline,
Phase-A import/contracts/choice checks, no PDF in any intermediate commit or payload.
The1000/100 limits and pinned hashes are real guards, not stale counts to generalize.

report_current reads an old fillinputs owner list, historical build folders and many
literal totals/statuses. Use the current bound summaries for owner/source/line/byte,
header/name/axiom/hole/print/seal/control/cache-root totals and milestone status. Keep
old review line maps as historical attribution; handle new files absent at the old
snapshot instead of git-showing them there. Do not claim current passes from oldM0.

finalize_m0_report is specifically the completedM0 reporter, with exactM0marker and
historical146/511/184guards/prose. Preserve that snapshot; add a checkpoint-aware final
assembler rather than rerunning it against proof-filled HEAD. All dynamic assertions
must compare independent expected sets, not each result against its own claimed total.
Report final remaining PhaseB hypotheses accurately; successful gate packaging is not
an unconditional sampler-efficiency proof. Derive cache roots from the current precise
import manifest, preserving narrowed refresh/host constraints; no frozen83assumption.

package_checkpoint has no22count, and already checks every intermediate commit for
PDFs, exact replay hashes/bundle, symlinks and both exact manifests. Keep these guards.
Tighten its loose startswith('.../Obfuscation') to the exact facade/directory boundary,
compare payload paths to the same complete inventory+approved export, and verify
report/evidence/source binding to the requested checkpoint HEAD. Preserve destination
scope and branch/bundle/replay checks. Do not package a stale report simply because
the current changed-file count looks right.

## 5. Minimal integration order and root-run validation plan

1. Freeze a committed current source snapshot; generate dynamic inventory once.
2. Prepare/reload static list; regenerate current collector and census probes from it.
3. Root serial builds all expected owners; source/hash/error coverage must be exact.
4. Regenerate all four FULL-closure seals and paired controls with unchanged payload
   adapters; bind new inventory and environment; run root serial matrix/controls.
5. Run exact matrix-set/control-coverage checks plus existing dynamic record guards.
6. Refresh full axiom graph/prints, frozen statements, source inventory/lint/scans.
7. Assemble current checkpoint report and reproduce complete package/replay/manifests.

Proposed negative tooling checks (not run): omit Basic from any owner/manifest/census;
duplicate one owner while keeping old cardinality; remove a variant; truncate ROOT
records; supply0planned probes; drop a requested chunk; reuse old environment/log;
final0holes TSV; unapproved helper/declaration change; stale report HEAD; forbidden
prefix path. Each must fail except the legitimate0holes TSV case, which must pass.

Pinned archived build_seals/build_controls contain59-module historical CLI guards.
Current job wrappers import their lexer/instrumenter functions, not those CLIs; do
not edit provenance code just to remove59. The required changes are job-level source
inventory and independently complete coverage checks. No guard/closure reduction is
proposed or implemented by this review.
