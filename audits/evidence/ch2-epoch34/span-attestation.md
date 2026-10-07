# Span attestation — Chapter 2, epoch-3/4 fill gate

Maintainer-side whole-span evidence for the epoch-3/4 proof audit. The
span is `b55180a8` (the tip on which the four E3 briefs were issued; the
post-gate serial queue D6/D7-deferral/E5-dedup had already landed) to
`9e9494aa` (the 4B fill). The one later commit at pack time is the 4B
attestation-records commit (`9cfedc45`), which touches no Lean source.

## 1. Commit census

Fifty-nine commits lie in the span. They decompose exactly as:

- **16 Codex fill commits in scope** (the per-commit table below) across
  **14 accepted zip deliveries** — the E3 wave (A partial, B 2-of-3, C,
  D), the E3 continuations (A-cont, A-cont-2, A-3 = run β of the
  disclosed duplicate dispatch, B-cont), and the E4 chain (4A, 4A-2,
  4A-3, 4A-4, 4A-5 in two ordered patches, 4B). One further delivery —
  run α of the duplicate A-3 dispatch — was **discarded whole** without
  integration (decision-log row of 2026-10-05; α archive SHA-256
  `a5d7948ee3e14749e2c27ae72a8ffd43dc547f39d93c29781dd6b5dcee99767f`,
  β `161e6cc7ea4b038294e3f51d52803d910acd462419b1f96973d2a08c24d2e9f1`;
  both zips retained in `ch2_local/epoch3/`).
- **4 Codex emitter-fill commits** (`bcee716b`, `200bdb91`, `634ee795`,
  `a10771fe`) — the emitter-increment sub-campaign, **out of scope
  here**: its statement gate closed in three rounds and its fill gate in
  one (`audits/emitter-infra-*`, `audits/emitter-fill-*`,
  both `…-resolutions.md` CLOSED). The e3/e4 fills' *consumption* of
  those contracts is in scope.
- **2 colleague merges** (first-parent rows in the table): merge #1
  (`e688a482`, verified `d7b5b6f9`) — the CNF/DNF carrier refactor and
  the colleague's own adaptation of the then-fresh 3D fill; merge #2
  (`53072100` bringing `f70c57c2`, verified `4e6e3e47`) — Arora–Barak
  ch. 6 pp. 106–115 plus private rewiring in nine campaign modules and
  the module-order extension 57 → 65.
- **Maintainer commits** (briefs, integration attestations, audit-gate
  records, decision-log/backlog upkeep): none touches any of the six
  owned sources. Programmatically asserted over the span: every commit
  with a nonzero numstat on an owned file is one of the eighteen rows
  below or one of the two colleague-authored commits (`132e79ee`,
  `f70c57c2`) whose content enters exactly through the two tabled
  merge rows.

## 2. The six owned files, endpoint to endpoint

| File | At `b55180a8` (lines/privates/sorries) | Now (lines/privates/sorries) |
|---|---|---|
| `ClassNP/Nondeterminism.lean` | 2,454 / 102 / 5 | 5,835 / 271 / **0** |
| `ClassNP/EXP.lean` | 2,534 / 115 / 1 | 3,268 / 147 / **0** |
| `ClassNP/SAT.lean` | 158 / 0 / 3 | 4,815 / 288 / **0** |
| `CookLevin/Snapshot.lean` | 252 / 0 / 5 | 368 / 4 / **0** |
| `ClassNP/Tautology.lean` | 133 / 0 / 2 | 1,749 / 95 / **0** |
| `CookLevin/Hardness.lean` | 237 / 0 / 5 | 9,937 / 618 / **0** |
| **Totals** | 5,768 / 217 / **21** | 25,972 / 1,423 / **0** |

The 21 base `sorry`s are exactly the 21 gate targets (15 E3: the
six-member padding cluster, the three-member SAT track, the five
snapshot-locality lemmas, `TAUTOLOGY_mem_coNP`; 6 E4: the five
Cook–Levin theorems and `TAUTOLOGY_coNPComplete`). All are now proved
with empty admission roots (§5).

## 3. Per-commit numstat over the six owned files

| Commit | Author / delivery | +/− on owned files |
|---|---|---|
| `bf6a06f8` | Codex, E3-A (partial) | +561/−2 |
| `3be8aed4` | Codex, E3-B | +1,213/−2 |
| `42f99b0f` | Codex, E3-B (reduction math) | +999/−5 |
| `c606476d` | Codex, E3-C | +121/−5 |
| `22f110b9` | Codex, E3-D | +1,146/−1 |
| `e688a482` | **merge #1** (first parent) | +35/−39 |
| `96d5b017` | Codex, A-cont | +1,395/−1 |
| `07bbad98` | Codex, A-cont-2 | +608/−2 |
| `1c824071` | Codex, A-3 (run β) | +1,580/−40 |
| `24bd4cd9` | Codex, 3B-cont | +2,488/−1 |
| `e3abb0d2` | Codex, 4A | +957/−1 |
| `a4ca9302` | Codex, 4A-2 | +919/−0 |
| `9f1808a6` | Codex, 4A-3 | +2,359/−0 |
| `8e2d7ee1` | Codex, 4A-4 | +2,975/−0 |
| `57507830` | Codex, 4A-5 patch 1 | +2,063/−0 |
| `06ce95fa` | Codex, 4A-5 patch 2 | +465/−37 |
| `53072100` | **merge #2** (first parent) | +217/−236 |
| `9e9494aa` | Codex, 4B | +476/−1 |

Arithmetic closes exactly: fills +20,325/−98, merge #1 +35/−39,
merge #2 +217/−236; net +20,204 = 25,972 − 5,768.

**Deletion ledger (the −98 across fills).** 21 target `sorry` lines;
A-3's 34 further deletions are its brief's **sanctioned restructuring**
of E3-A's unproved in-source scaffolding (integration row 2026-10-05);
4A-5 patch 2's 33 further deletions rewrite **two proof bodies from its
own patch 1** (the disclosed `delta`/strong-induction surface fix —
nothing inherited was touched, verified by the patch-pair replay); the
remaining single-digit deletions are the E3 wave's disclosed
docstring/blank splices, itemized in the integration rows. Every
delivery's deleted lines were audited one by one at integration before
`git am`.

**Merge decomposition.** Merge #1's −39/+35 is the colleague's
adaptation of the day-old 3D fill to the refactored carrier plus the
`TAUTOLOGY` definition retype (kernel-verified at `d7b5b6f9`; the
retype is a ride-along review item of this pack). Merge #2's
−236/+217 rewires **privates** in `SAT.lean`/`EXP.lean` toward the
colleague's new shared modules and **adds two public declarations to
`EXP.lean`**: `enumWord` (promotion of a former fill private) and
`exists_proj_decider` (new). No public declaration was deleted or
retyped by merge #2 anywhere; verified per-file at `4e6e3e47`.

## 4. Freeze and surface

- Every accepted delivery passed, at integration: archive SHA-256
  manifest; per-patch deleted-lines audit; **byte-identical
  format-patch replay in an isolated worktree** (tree and blob hashes
  matching the REPORT claims) before `git am -3`; brief-copy provenance
  (the zip's embedded brief byte-identical to the committed brief, from
  4A-3 on).
- Name-level public surface of the six files across the whole span:
  **unchanged by every fill** (all 1,206 net new source declarations
  are private; kernel-level checks additionally cover generated
  declarations — the A3/A5/4B traversals assert "surface = the public
  theorems only"), and changed by the merges only as itemized above.
- Statement freeze: every target's statement and docstring byte-frozen
  through its fill, except the one recorded carrier retype of
  `TAUTOLOGY` by merge #1 — after which `TAUTOLOGY_mem_coNP` (filled
  pre-merge) was adapted **by the colleague** and kernel-reverified,
  and both later Tautology targets were filled against the retyped
  definition.

## 5. Elaboration and axioms

- Fresh-olean ordered sweeps at **every** integration, zero `error:`
  lines each, admissions on the six owned files stepping 21 → 13 → 6 → 5 → 5 → 5
  → 5 → 1 → **0**, each step predicted before its sweep and matched
  exactly (the emitter sub-campaign's own statement-layer admissions
  rose and fell between the 13 and the 6, inside its own closed gates;
  that stepping is recorded in the emitter gate records).
  Final states: `audits/logs/e4A5-closure-sweep.log` (57/57, one
  admission), `audits/logs/colleague-merge2-sweep.log` (65/65 after
  the order extension, with the honest mid-log first-attempt failure
  that motivated it), `audits/logs/e4B-closure-sweep.log` (65/65,
  **zero sorry warnings**).
- Kernel closure traversals at every integration (committed programs
  for the two closure gates: `audits/programs/ch2-e4A5-ClosureAxioms.lean`,
  `audits/programs/ch2-e4B-ClosureAxioms.lean`): all 21 targets now
  print **empty admission-root sets** with axioms at most
  `propext`/`Classical.choice`/`Quot.sound`; whole-module no-allowlist
  enumerations (Hardness 1,550 checked declarations; Tautology 439);
  and the final whole-surface pass — **11,436 checked `TCSlib`
  declarations across the 65-module import closure, zero `sorryAx`**.
- Policy: lint 0 FAIL throughout; the in-scope size WARNs are the five
  recorded exceptions (Nondeterminism 5,835; SAT 4,815; EXP 3,268;
  Tautology 1,749; Hardness 9,937), each justified at integration
  under exclusive single-file fill ownership and queued for the
  approved post-gate routine-layer retrofit.

## 6. Deviations on record (all disclosed at integration)

1. The 4A chain ran four verified partial checkpoints before closure,
   each inside the briefs' continuation provisions, each banked
   admission-free; 4A-5 honored the sanctioned output-identity
   checkpoint by committing and checking patch 1 before any semantics.
2. The duplicate A-3 dispatch (user-disclosed operator error): both
   runs complete and protocol-clean; β selected on the recorded
   criteria (integrity tie → audited-surface consumption → route
   fidelity → economy); α discarded whole, never hybridized.
3. Container shims and cache recoveries: the `/proc/<pid>/exe`
   compatibility shim disclosed by the A2–A5 and 4B hosts (source
   included in each zip; never entered the repository; superseded by
   the maintainer's independent fresh sweeps on an ordinary host); 4B's
   `leantar` extraction recovery through the official hash-keyed cache
   APIs with pins unchanged.
4. The A2 brief's scoping contradiction (maintainer error, escalated by
   the agent, resolved by reordering into A-3) and the two in-flight
   kernel-surface fixes (A3, A5: autogenerated equation lemmas for
   imported definitions removed by direct `delta` unfolding) are on
   record in the decision log.
5. One count discrepancy for the record: the E3-D integration row
   recorded "68 privates"; the file-truth name inventory (and 4B's
   freeze audit) counts 67 inherited Tautology privates. The name-level
   inventories are authoritative.
