# External audit pack — machine-routine layer (§12), epoch F2 fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4c), the
§12 fill campaign's second and final epoch. The statement gate closed in
three rounds (`audits/routine-infra-resolutions.md`); epoch F1 closed in one
(`audits/routine-f1-resolutions.md`). This round audits the **F2 fills**:
the 19 Catalog space rows, delivered in two batches by the same agent
lineage — F2A (17 of 19 in the prescribed risk order, a ground-rule-7
partial) and the continuation A2 (the two frontier targets:
`exists_loopTM_spaceUsed` and `computesFunInTime_pairMapSnd_spaceUsed`).
With these 19, **all 56 audited-true statements of the §12 layer are
proved**: `Build/Embed.lean`, `Build/Seam.lean`, and `Build/Catalog.lean`
are zero-sorry. Epoch gates follow the statement-gate rule: the gate closes
on a round with zero blockers and zero majors (`workflow.md` §4); this
close completes the routine layer.

Audited at commit `41a06e08` (branch `complexity/arora-barak-ch3-4`). The
fills are the two attached patch series (Codex-authored, integrated by
`git am -3` as `64f02699` for F2A and `97daf8a5` + `47880f58` for A2); the
agents' own `REPORT.md`s are attached verbatim. **Every proof is
kernel-checked** — the maintainer's replay evidence is below — so this
audit's object is not correctness of the checked terms but the **surface**:
the 351 new private declarations (F2A 306, A2 45), the honesty of the
helper statements (a vacuous or subtly weakened private lemma misleads
every later fill that imitates it), fidelity of the proofs to the binding
inherited space ledgers, and the declared anomalies below.

## Brief for the auditor

1. **Blind-restate the 45 A2 private declarations individually** from their
   bodies (the A2 report's role tables are claims to check, not ground
   truth): the forwarding controller stack (`a2_MapState`/`a2_mapAct`/
   `a2_mapTM` and the `a2_mapCfg`/`a2_mapVirtual` configuration shapes),
   the parse/buffer/rewind/emit stage lemmas (`a2_map_first` through
   `a2_map_setup`), the virtual-input lockstep pair (`a2_mapVirtual_step`/
   `a2_mapVirtual_run`), the seam-identification family (`a2_mapEntered`,
   `a2_mapSetup_*`, `a2_map_launch`, `a2_map_reject`), the space engine
   (`a2_map_space`, `a2_map_sum`, `a2_mapSumEquiv`), and the loop-ledger
   family (`a2_source_radius`, `a2_heads*`, `a2_call_*`, `a2_fuel_heads`,
   `a2_loop_*`, `a2_segments`).
2. **Blind-restate the F2A privates by family, every load-bearing member
   individually**: the witness machines (`f2_idTM`, `f2_constTM`,
   `f2_catalogPrefixTM`, `f2_pairValidTM`, `f2_pairDupTM`, `f2_incFixedTM`,
   `f2_pairExtractTM`, `f2_counterTM`, `f2_pairCountTM`, `f2_timedCondTM`,
   the reopened `f2_loopHost` controller); the trajectory/space engines
   (`f2_space_of_time`, `f2_poly_space`, `f2_counter_space`,
   `f2_segment_heads`, `f2_seamed_space`, `f2_space_radius`,
   `f2_cond_ledger`/`f2_branch_space`/`f2_cond_space`,
   `f2_exists_loopFind_space`, `f2_rewind_heads`, `f2_strip_linear`); and
   the `catalog_redirect*` projection copies. The F2A report's per-target
   routes are the claims to check.
3. **Check contract fidelity against the binding ledgers**:
   (a) the loop target against the statement-round answer-5 six-step
   ledger (quoted verbatim in `briefs/routine-f2-batchA2.md`): the chosen
   constant multiplies `S n + T n + 1` **jointly**, the round count
   `R n` appears in the time clause only, and **no space quantity
   accumulates round to round** — verify from `a2_segments`/
   `a2_call_heads` that one fixed common interval covers all rounds and
   halted tails; (b) the `pairMapSnd` target against the R4 ledger: the
   witness is the commissioned forwarding controller (the round-1-refuted
   captured-output `pairMapTM` witness must appear nowhere in the proof),
   the payload bank's contribution carries **coefficient one** on `Sg`
   via per-tape visited-set containment in the source's own visited set,
   both virtual-input boundary clamps hold including empty `b`, forwarded
   output is never stored on a work tape, the malformed branch halts
   silently inside the setup bound, and the frozen time clause
   `c*(n+1+Tg n)` is untouched; (c) the seventeen F2A rows against the
   round-1 assessment rows they cite: R5's zero-constant/zero-exponent
   boundary absorption in `polyBits`, R8's linear-before-weakening strip
   bound, split search's candidate count multiplying time but never the
   space interval, and W3's exact coefficient-one
   `sD(n) + max(s₁(n),s₂(n)) + c` conditional ledger.
4. **Check the usage discipline of `f2_space_of_time`**: the report claims
   it is an actual all-time trajectory proof (halted-endpoint
   identification, time-prefix image, `T+1` positions per tape) used only
   where a sharper received time bound already fits the space envelope —
   verify it never infers an all-time bound from a final configuration
   alone, and that the direct counter, unary banks, split-search seams,
   and conditional banks genuinely carry their separate invariants.
5. **Assess the declared anomalies**: (i) the dual-mode controller —
   `a2_mapTM` takes a `forward : Bool`, and the auxiliary `false` mode
   freezes at the live payload entry, used only to certify the first
   seam arrival while the theorem's witness is always the `true` mode;
   is this one-machine-two-modes design a faithful instance of the
   commissioned controller, and does any stated property of the `false`
   mode leak into the exported contract? (ii) the private copies —
   A2's `a2_mapSumEquiv`/`a2_map_sum`/`a2_loop_halted_run` and F2A's
   `f2_`-prefixed reopened implementations (Loop/Primitives/Wrappers
   transition tables) — are the copy-role claims accurate, and is the
   dedup queue (the recorded 12.2c split plus the queued `Wrappers`
   head-trajectory projection) the right home for them? (iii) both
   deliveries again carried an environment-shim C file
   (`environment/self_exe.c`, an `LD_PRELOAD` `/proc/self/exe`
   workaround per their reports) — **excluded** (not compiled, not run,
   not integrated, unreferenced by the patches); flag if any integrated
   artifact nonetheless depends on anything outside the Lean sources;
   (iv) the loop proof's deliberately conservative common interval
   (administrative segments widen the radius by their fixed duration) —
   confirm the widening is a fixed per-call allowance, not a per-round
   accumulation in disguise.
6. Report anything the fills newly misstate — in the standard table and
   severity scale. Statement bodies were frozen; verify no signature,
   definition, or docstring drift against the attached patches (the
   maintainer's checks: F2A freeze re-established by **direct content
   comparison** — all 72 pre-F2A declarations verbatim and in order, the
   diff's apparent non-sorry removals being Myers-pairing artifacts; A2
   removed exactly two lines, both `sorry` bodies, with all 378 base
   declaration heads verbatim and in order).

## Repository-side attestations (verify or challenge)

* Freeze (maintainer): F2A — single-file patch, direct-content
  verification as above; A2 — both patches touch only
  `Build/Catalog.lean`, exactly two removed lines across both (the two
  frontier `sorry` bodies), and the delivered full source is
  byte-identical to the integrated file. No public declaration added,
  removed, or restated in either delivery; all 351 new declarations are
  `private`.
* Fresh replays: F2A (`audits/logs/routine-f2a-integration-sweep.log`) —
  0 `error:` lines, **exactly 2** `declaration uses 'sorry'` warnings, the
  two frontier rows; final A2 state
  (`audits/logs/routine-f2a2-integration-sweep.log`, run at `41a06e08`'s
  parent set) — `Catalog` and the `TuringMachine` facade both exit 0 with
  **zero** errors and **zero** sorry warnings, fresh `.olean`s.
* Independent axiom prints (maintainer-generated, not the agents'):
  `audits/logs/routine-f2a-axioms.log` (interim: 18 clean, `sorryAx` on
  exactly the two then-open frontier rows) and
  `audits/logs/routine-f2a2-axioms.log` (final: **all 20** Catalog space
  theorems — the 19 F2 rows plus the F1 W2 row — exactly
  `[propext, Classical.choice, Quot.sound]`; `sorryAx` nowhere).
* Style lint (`audits/logs/routine-f2a2-stylelint.log`): 0 FAIL;
  `Catalog.lean` at 10,876 lines WARNs — the queued per-theme split
  (backlog §2 decision 12.2(c)) is the recorded justification; the
  `Loop`/`Primitives` WARNs predate this epoch with recorded
  justifications.
* Delivery integrity: F2A `SHA256SUMS` 14/14 OK, bundle verifies against
  its recorded base `ead9abf1`; A2 `SHA256SUMS` 20/20 OK, bundle verifies
  against its recorded base `3099ad2a`, and the A2 patch replay
  reconstructs the delivery tree exactly.
* Integration by `git am -3`, Codex authorship preserved (`64f02699`;
  `97daf8a5`, `47880f58`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/routine-f2-findings.md`; the epoch gate closes on zero blockers
and majors, which completes the §12 routine layer (56/56) and unblocks
the plan §4b stages that consume it.
