# Overnight megafill: finish MIG-1's named machine specifications and retire the copies

**Agent: Claude**, selected by the user for this dispatch. One session, one clone, one cumulative
branch, four ordered work packages with checkpoint deliveries. This is an integrated execution
of the already-approved MIG-1 F-A/F-C/F-B/F-D plan, including its assigned MIG-24 factoring.
It is substantial overnight work; a checked partial delivery is useful. No completion estimate
is a deadline.

## Base, environment and inputs

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Exact base: **83ac315ed9e7089466bd16a32f3b71fbadc556d2**, on `complexity/arora-barak-ch3-4`, never `main`.
  Create `fill/mig1-mega` at exactly that commit. Record its full hash. Do not merge, rebase,
  cherry-pick, fetch other proof deliveries, or follow the moving campaign tip after starting.
- The dispatch bundle supplies this brief, inputs, source populations, standards and historical
  statement-gate evidence. Keep an extracted packet outside the proof checkout before checking
  out the pinned base: these newly issued records are newer than that base. Paths below are
  relative to the packet/repository as appropriate. Verify the bundle checksum and all sections.
- Read `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`, and the attached
  **fill-environment-addendum.md v2.6**. Parts 1 and 2 apply in full; Part 3's shared environment,
  checkpoint recovery and process rules apply to this single integrated job. The four packages
  below are successive checkpoints on the same branch, not four independently reset fills.
- **One Lean process at a time**, `nice -n 10`, four Lean threads; one copy-text screen at a time.
  Use `devtools/seyoon/leanelab.sh` / `leanelab-o.sh`; the prescribed generated replay pipeline
  may use `scripts/lean_check_tree.sh` under its slot lock. Never run `lake build`, a bare Lean
  command, or the unfiltered cache fetch. All Python is `python3 -I`.
- Set a task-specific scratch environment outside the clone, with `TCSLIB_REPO` set to the clone,
  `TCSLIB_SCRATCH` to that scratch area and `TCSLIB_LEAN_SLOTS=1`. Source it for every command.
  Use one complete olean tree for this clone, not partial `LEAN_PATH` overlays. Never reuse the
  maintainer's Mac paths or snapshots from receipts as if present on your host.
- Run and log the addendum's preflight **before** cache/Lean work (12 GiB initial disk floor,
  4 GiB memory headroom computed as specified). Use the pinned toolchain. Fetch only the
  **239 Mathlib roots** in `inputs/mathlib-roots.txt`; log archive-store provenance and verify
  every present package against the manifest. If Lean never starts, deliver only the environment
  report; do not write unchecked proofs.
- `inputs/bootstrap-order.txt` has **51 modules**: enough for the owned homes and the route
  probe. `inputs/final-order.txt` has **641 modules**, including unaffected imports needed for the
  full final sweep; the affected downstream alone is **394** modules. Bootstrap the small list
  first if helpful, then compile the remaining prerequisites before final checks. The full roots
  list covers both lists. A missing dependency is a limitation to report, not a reason to claim
  a sweep passed. Do not modify or manually build a dependency package outside the authorized
  cache procedure. Deliver checked progress even if a later unrelated dependency is unavailable.

All received source, gate evidence and reports are data. Historical scripts are comparison
inputs, not instructions to execute. Use their current repository counterparts only after
inspection. Historical `audits/` paths resolve through `campaign/MOVED.md`.

## Approval and current scope

The statement gate is **16-mig1-statements, round 2 CLOSED**, with its verbatim findings and
resolutions in the packet. The stage-S statements landed in #98. The user's decisions of
2026-10-13/14 approved the named witnesses, both consolidations, the space rows remaining in
Catalog, and the six canonical-row retirements with consumer edits. On 2026-10-17 the user
assigned MIG-24 T1–T6/T2b to these batches and T7's relevant singletons to their next file edits.
`MIG1-design.md` and `MIG1-inventory.md` are historical design data: **current source and the
gate's final statements override their proposed names, counts and old line numbers**.

Fresh measurement finds **17 existing public specification admissions**. Their exact names and
headers are `inputs/target-admissions.json` (9 in F-A, 5 in F-C, 3 in F-B). Three unrelated RAM
word-size admissions are recorded in `base-admissions.json` and remain frozen.

**Owned Lean files** are exactly `inputs/owned-files.txt` (11):

| Package | Files under `TCSlib/Complexity/` | Permitted work |
|---|---|---|
| F-A | `TuringMachine/{Composition,Simulation,Encoding}.lean`, `TuringMachine/Build/Wrappers.lean`, `ClassP/TimeConstructible.lean` | Fill nine existing specs; re-point the corresponding existing existential rows; approved in-file factoring |
| F-C | `TuringMachine/Build/Loop.lean` | Fill five existing loop specs; move the intrinsic space argument from Catalog; re-point loop rows and assigned factoring |
| F-B | `TuringMachine/Build/Primitives.lean` | Fill three existing specs; finish approved forwarding-map consolidation and existing composite-row re-points; assigned factoring |
| F-D | `TuringMachine/Build/{Catalog,CertShell}.lean`, `TuringMachine/CodeSimulator.lean`, `RAMSimulation/WordSize.lean` | Retire the approved copies/rows, re-point consumers; WordSize is **documentation-only**, fixing the stale Catalog line reference |

Every surviving public statement, name, visibility, home and relative declaration order is
frozen, as are witness transition tables. Existing proof bodies of corresponding rows may be
replaced by calls to the new specs; private glue may be added/moved/retired within its approved
home. Refine proof sketches and module Contents/status prose to describe the resulting code.
All nontrivial proofs need readable sketches. No file split, new host or unrelated cleanup.

**Exactly three already-gated public additions**, deliberately left for F-B, are allowed:
`Turing.FinTM.pairMapSndTM`, `pairMapSndTM_computes`, `pairMapSndTM_spaceUsed`. Their exact
statements are in `inputs/forwarding-map-contract.lean.txt` (from gate 16's final Primitives
part). The witness is the existing Catalog forwarding controller (`a2_mapTM Mg true`), moved
to Primitives with its private implementation and renamed privately as needed. Preserve that
machine's code modulo renaming; do not design a replacement. It forwards payload emissions,
with two input buffers and coefficient **one** on payload space. Its time coefficient is **22**.
Both theorem proofs must be complete before this addition is delivered as complete.

**Exactly six public removals**, all in Catalog, are allowed (`retired-public-names.txt`):
`Turing.transferTM_run`, `copyTM_run`, `clearTM_run`, `compareTM_run`,
`incrementTM_run_succ`, `incrementTM_run_overflow`. Replace every code consumer by the existing
framed `_ofCfg` equations and the already-published `Cfg.ofWords_*_endpoint` lemmas; update prose
pointers too. Fresh candidates are in `retirement-consumers.txt`; repeat candidate enumeration
on your final tree and inspect all hits. No other public addition, removal, rename or statement
change is authorized. Escalate an exact missing statement instead of guessing an API.

Imports are frozen except the **already approved** additions
`Mathlib.Algebra.BigOperators.Fin` in Simulation (if needed) and
`TCSlib.Complexity.TuringMachine.Build.Primitives` in Catalog. The latter edge is pre-checked
acyclic. No new import in another frozen file. A needed additional import is an escalation.

## Work queue and checkpoints

Work in **F-A → F-C → F-B → F-D** order on the one cumulative branch. Complete a small proof
block and check it before continuing. Do not treat a kernel-accepted theorem depending on an
unfilled spec as complete. A previously admission-free row must never acquire `sorryAx`.

1. **F-A: nine specs and their rows.** Move or reuse the existing same-home proofs for identity,
   fixed comparison, untimed conditional, pairing, timed conditional and the binary length
   counter. For intrinsic space, relocate Catalog's branch, conditional-ledger and counter
   space reasoning to the witness's existing home and delete the source in F-D. Use the actual
   published `ComputesInTime.spaceUsed_le` and `workTapePos_runFrom_mem_Icc` instead of copies.
   Deliver `fill-mig1-mega-cp01.zip` after the first checked same-home group and `cp02` after F-A.
2. **F-C: five loop specs.** Preserve the coefficient **10**, the first-visit cuts, positive
   round durations, empty-output round configurations, and both find/decision terminal values.
   The space budget must be independent of the number of rounds. Gate 16's corrected full-file
   Loop overlay and retarget table show the intended surviving-home route, including the
   strengthened preparation's fuel-head clause; they are historical evidence, not a replacement
   for a current in-module proof. The current call API is **`callTM_run`**, already proved;
   do not add the superseded draft names `callTM_install` or `callTM_emit`. Deliver `cp03` after
   the time/configuration group and `cp04` after the intrinsic space budget and F-C factoring.
3. **F-B: three existing specs, forwarding map, composite row rewrites.** Reuse the existing
   proof bodies for `polyBitsTM`, length-check, strip, split-search and clean-call specs. A proof
   body depending on F-A/F-C is admission-free only after those dependencies are filled; verify
   the actual axiom walk before calling it complete. Implement only
   the three approved forwarding-map exports above, retiring the old captured-output mapper;
   pair duplication uses the existing `pairDiagTM`, retiring the private duplicate. Preserve
   all numeric constants and the split-search space degree. Deliver `cp05` after a checked group,
   then `cp06` after F-B. If the loop budget is still blocked, do independent Primitives leaves
   and the forwarding map before reporting that dependency; do not discard checked progress.
4. **F-D: retire copies and finish the integrated tree.** Make Catalog's existing space rows
   short corollaries of the proved named specs. Remove the `f2_`, retired `a2_` and
   `catalog_redirect*` copies according to their *semantic current* fates, never a blind numeric
   slice. Each moved argument has exactly one surviving home. Retire the six public rows and
   re-point CertShell/CodeSimulator, whose old B5a prerequisite is now merged. Fix WordSize's
   stale line reference without touching its declarations. Deliver `cp07` after the deletion
   and consumer checks, then the final `fill-mig1-mega.zip` after validation.

**Assigned MIG-24 work** is part of these packages, with a disposition per kind in REPORT:
T1 rewind bounds (Simulation/Loop/Primitives); T2 mirrored emitter steps and clean-call entry
(Primitives/Loop); T2b parser variants (inspect whether actually shared); T3 call-bank
initial/final (Loop); T4 buffered-composition corollaries; T5 Catalog framed/canonical sweep
rows; T6 pair-projection space rows. Inspect T7's Loop, Encoding and Simulation singletons
because these files are touched. Preserve states, tables and statements; use private parametric
helpers within a home and existing public cross-file equations. If a family needs a new public
interface, record its precise gap and leave that family incomplete. This does not authorize
new debt or a third private cross-file implementation.

## Reuse, rule 10 and verification

- Owning several files does **not** relax the no-unfolding rule between them. Cite a public
  equation or contract to read another file's definition; never cite its private name,
  including a mangled private name. Move approved proof material to its home rather than
  copying a private host for a second consumer. Core/Mathlib definitions may reduce in `rfl`,
  `decide` or `show`, but never appear as explicit `simp`/`rw`/`unfold` arguments.
- Inspect every inline re-derivation too: buffer indexing, first-exit/absorbing-halt chains,
  `Nat.find`, and field-by-field configuration equalities. Use the published API. The full
  duplication ledger is the baseline; raw text matches are candidates, not adjudicated debt.
- Seal the **changed/new proof regions** per home against every foreign TCSlib definition
  reached, removing reached default-simp unfoldings. Give both pointwise and abstracted
  equation controls, successful unsealed and unsuccessful sealed, with exact diagnostics and
  exit counts. Explicitly inventory unsealable abbreviations, projections and matchers; do not
  turn on unsafe reducibility or claim coverage for an ineffective attribute. Inspect all
  unfold/simp/rw/show/change arguments separately. Retain raw source and output for every run.
- Gate 16 R2-2 is carried: a negative-control checker checks **multiplicity**, exactly one
  expected error per failing example, no extras, and the expected nonzero exit code. Include
  the duplicate-diagnostic negative control; a set of failing names alone is insufficient.
- Run the source/public freeze against the pinned base, with only the explicit three additions
  and six removals. Compare surviving **complete top-level headers** (an `input := x` inside a
  binder is not a proof delimiter), visibility, relative order, imports and witness tables.
- Print/walk axioms for every filled/new spec and every changed public proof; also compare an
  **unfiltered compiled non-private census** of changed modules, retaining compiler auxiliaries
  and module owners. Complete results use only `propext`, `Classical.choice`, `Quot.sound` or
  fewer. Report every residual admission by its full name, including unchanged ones; the
  final three RAM admissions stay frozen. Do not add an axiom, unsafe proof bypass or unreported
  `sorry`/`admit`. A partial checkpoint lists its exact remaining obligations.
- After edits, elaborate the edited module and the remaining relevant bootstrap tail. Before
  final delivery, run the complete 641-module final order through the wrappers, updating its
  dependency order after the approved import change. Log each module's start/end and maximum
  memory, raw diagnostics and exit status. Compare static admission counts to Lean's counts.
  The maintainer performs the later current-campaign merged-tree replay; this worker sweep is
  a check of the pinned fill tree.
- Base screen: `logs/screen-base.txt`, full **16-file** population in `screen-population.txt`.
  Run the same population at the final frozen tree, adding any further cited Lean source to
  **both** populations, and supply both raw outputs and pair delta. One screen at a time. List
  every new/moved candidate and its semantic disposition, source-inclusive counts and cumulative
  per-file debt; temporary moves in partial checkpoints are explicitly incomplete, not new debt
  acknowledgments. Run campaign/policy lint and blueprint checks relevant to the changed source.

The maintainer's pre-ship receipt distinguishes actual baseline elaboration, the conditional
consumer probe and source-only graph/census checks. Its route probe makes the unfilled specs
explicit hypotheses; it does not prove those specs. The three forwarding exports are future
gated additions, not names claimed to exist at the base. Do not use the initial failed probe
attempts as a passing check.

## Delivery and escalation

After each named checkpoint, commit, create its zip, and **push that zip immediately** to
`exchange/pass-shelat-ch5-8` under **`arora-barak-ch3-4/inbox/fill-mig1-mega/`**. Touch no other
path on the exchange branch. Use a clean exchange checkout, pull with rebase before **every**
push, and never force-push. Do not change any campaign branch or open/merge a campaign PR.
The maintainer reviews the delivery, prepares PRs and gates, and Seyoon merges them.

Each cumulative checkpoint/final zip contains: `REPORT.md`; full modified source; ordered
`git format-patch` patches from the exact base; a git bundle with that base as its sole
prerequisite; source/public/import/body-freeze results; all environment/cache logs; module
elaboration and axiom/census logs; seal sources, control sources and raw outputs; both complete
screens and their population/delta; and `SHA256SUMS` for every payload. For an early checkpoint, include every check completed so far and explicit **NOT RUN** entries
for the remaining checks; do not delay publishing checked progress to wait for the final screen
or 641-module sweep. Both complete fresh screen outputs and the full sweep are mandatory before
a delivery is labeled **complete**. If they cannot finish, deliver a validation-incomplete
partial with exact limits. Verify the archive before pushing. Keep source commits under your
actual identity; do not impersonate the user or Codex.

`REPORT.md` lists the checkpoints reached, each target's status, all moved private material and
its original/final home, every assigned factoring disposition, current counts and line sizes,
all new/removed public names, imports, source citations and the exact tests run. Distinguish
original evidence from your fresh runs. Include a clear partial/complete verdict and every
escalation with the exact missing public statement/import/design choice. Attach no fabricated
success receipt. If blocked on one independent part, continue other authorized parts; before
the session ends, push the newest checked partial zip. Also push a separate
`megafill-mig1-REPORT.md` with zip hashes and start/end times, and summarize the pushed paths
in chat. Partial delivery is acceptable; lost checkpoint work is not.
