# derand · checkpoint 1

Issue: issued-r2, replacing `outbox/fills/derand/` r1. Worker: Codex, the worker
called “Claude” by the brief. The verified host addendum takes precedence where stated.

## Status

Source base: `01de2d8baed9113e4a099e13c5d50c81e6dbc66f`. Checkpoint tip: `776dabdabb276c75b98780e5018275fbcdc25e3a` on the local-only `fill/derand` branch.
The delivery contains the generic-fuel harvest E1, the two pre-approved readers E2/E3,
the specifically approved SR-01 reader, and the DTIME corollary proved from H17.

| Target at this checkpoint | Status |
|---|---|
| `Complexity.exists_seedMajorityTM` | original admission retained |
| `Complexity.seedMajority_mem_DTIME` | proved modulo `exists_seedMajorityTM` |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | original admission retained |

The full issued 377-module replay passed with zero errors. Its sorry list is exactly
the issued baseline minus `seedMajority_mem_DTIME`: 25 declarations in 12 modules.
The source branch stays local. Later consumer/host work is outside this checkpoint patch.

## Rule 10 finding and exception disclosure

**Rule 10 status: HOLD.** All four full-closure harvest variants report 20 diagnostics:
11 belong to the byte-unchanged original `polyTimeComputable_find`, and 9 belong to E1.
Eight new diagnostics concern the hidden tape/state carrier fields of the imported
`ModuleHost.hostTM` and `IterateFind.copyTM`; the last concerns the final opaque
function-computation transport. The raw logs and source line maps are delivered at
`evidence/verification/seals/checkpoint1-harvest-final/`.

The other edited files pass their four focused seals. All paired controls pass
unsealed and their sealed negative fails exactly once; the controls are retained in
the final delivery, with checkpoint-compatible DTIME imports. The explicit-unfold
scan found no added foreign-definition selector sites. A seal finding is reported
as a finding; the native and axiom checks are separate evidence.

SR-02 proposes typed interface views in two additional frozen providers. Automatic
approval review refused application; neither provider was edited. Seyoon delegated
judgment over exceptions while away. The worker continues the authorized mathematics
and records the uncleared interface finding rather than expanding provider scope.
This checkpoint requires maintainer review of that exception. The exact proposal,
failed/successful diagnostic prototypes, rejection, and pending status are included.

## Source files and sketches

| File | Base lines | Checkpoint lines |
|---|---:|---:|
| `TCSlib/Complexity/ClassP/DTIME.lean` | 117 | 135 |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | 556 | 799 |
| `TCSlib/Complexity/Randomized/Classes.lean` | 1403 | 1415 |
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 234 | 233 |

The corollary's status/sketch now describes its reader-based witness proof. E1 has
its formula and generalized assembly sketch. Existing target headers, definition
bodies, declaration order, and all frozen proofs remain unchanged; the header check
reports zero differences over 93 base declarations. Its one-character negative
control reports exactly one changed header.

## New declarations and full final signatures

E1 permits an arbitrary numerical fuel `R`, computed in binary by the supplied
machine `F`; it retains the total length guard and arbitrary initial word. Its
explicit polynomial per-round budget is `A * (2*n+2+P.eval n+5)^D`. The time is
`c*(T n+1)*(R n+2)`. No use of `final_bound` is made for exponential fuel.

### `Complexity.IterateFind.computesFunInTime_find`

```lean
Complexity.IterateFind.computesFunInTime_find :
∀ {g : List Bool → List Bool},
  Complexity.PolyTimeComputable g →
    ∀ {acc : List Bool → Bool},
      (Complexity.PolyTimeComputable fun s => [acc s]) →
        ∀ {out : List Bool → List Bool},
          Complexity.PolyTimeComputable out →
            ∀ {init : List Bool → List Bool},
              Complexity.PolyTimeComputable init →
                ∀ (R : ℕ → ℕ) (P : Complexity.PolyExpr),
                  (∀ (x : List Bool), (init x).length ≤ P.eval x.length) →
                    ∀ (F : Turing.FinTM Bool) (aF dF : ℕ),
                      (F.ComputesFunInTime (fun x => (R x.length).bits) fun n => aF * (n + 1) ^ dF) →
                        ∃ M c A D,
                          M.ComputesFunInTime
                            (fun x =>
                              match
                                List.find?
                                  (fun i =>
                                    acc
                                      (Complexity.pairSndD
                                        ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x)))))
                                  (List.range (R x.length + 1)) with
                              | some i =>
                                out
                                  (Complexity.pairSndD
                                    ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x))))
                              | none => [])
                            fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)
```

### `Complexity.mem_DTIME_iff`

```lean
Complexity.mem_DTIME_iff :
∀ {T : ℕ → ℕ} {L : Language Bool}, L ∈ Complexity.DTIME T ↔ ∃ c M, M.DecidesInTime L fun n => c * T n
```

### `Turing.FinTM.decidesInTime_iff`

```lean
Turing.FinTM.decidesInTime_iff :
∀ (M : Turing.FinTM Bool) (L : Language Bool) (T : ℕ → ℕ),
  M.DecidesInTime L T ↔ ∀ (x : List Bool), M.ComputesInTime x [Turing.MultiTapeTM.indicator L x] (T x.length)
```

### `Randomized.inBPP_iff`

```lean
Randomized.inBPP_iff :
∀ (E : Randomized.VerifierModel) (L : Language Bool),
  Randomized.InBPP E L ↔
    ∃ M a k,
      E.Eff (Randomized.boolVerifier M) ∧
        ∀ (x : List Bool),
          (x ∈ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = true) ∧
            (x ∉ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = false)
```

## Overlap and reuse

* E1 deliberately repeats the generalized assembly of the existing
  `IterateFind.polyTimeComputable_find`, as the brief expressly requires. It reuses
  the existing private `Inv`, `inv_*`, `verdictWord`, `stepWord`, `outWord`, and
  their lemmas in place. It does not copy their definitions, introduce a competing
  loop engine, or change `polyTimeComputable_find` or `final_bound`.
* Its machine implementation uses the published proved `exists_loopFindTM`,
  `ModuleHost.clean_install`, `clean_emit`, `host_call`, `host_clean`, `guard_add`,
  and request budgets. It does not consume admitted loop-host/conditional specs.
* E2/E3 and SR-01 expose existing definitions by `Iff.rfl`, with no attributes.
  The whole-base namespace-resolved scan found no collision in 1,274 Lean files.
* The corollary uses only the host contract and `mem_DTIME_iff`; it does not unfold
  `DTIME`, `DecidesInTime`, or `DecidesInTimeVia`.
* The SR-02 prototypes are feasibility experiments, not accepted home-file reader
  proofs. Their operational transition tables are not copied into the patch.

## Scope requests

### SR-01 · approved

The exact session question and answer follow verbatim:

```text
User reply received in this Codex chat, 2026-11-15 PST:

Question:
Approve SR-01: add only `Randomized.inBPP_iff` beside `InBPP` in `TCSlib/Complexity/Randomized/Classes.lean`, proved by `Iff.rfl`? It exposes the existing verifier, coin-schedule, efficiency, and 2/3 correctness witnesses without changing any definition or existing statement. The concrete patch is `/private/tmp/derand-worker/scope-inbpp-reader.patch`. The brief’s Scope rule requires your approval for this fourth shared-file addition; it also needs an exception for Classes.lean’s inherited length above 1000 lines. The three pre-approved additions and checkpoint-1 work continue while this is pending.

Answer:
Approve SR-01 and the inherited file-size exception
```

### Standing exception instruction

```text
User instruction received in this Codex chat, 2026-11-15 PST, verbatim:

I am going to be asleep and away from the keyboard. Use your best judgment when it comes to exceptions, and disclose them completely and transparently in your checkpoints and delivery. You are free to message other workers to coordinate access to shared Mac resources (and the cap of 3 Lean processes) as you see fit.

Worker interpretation:
Narrowly necessary exceptions may be decided without a further keyboard approval,
with exact changes, reasons, and validation disclosed in checkpoints and delivery.
The frozen target statements, shared three-Lean-process cap, own-tree isolation,
delivery-path restriction, and no-force-push rule remain in force.
SR-01 already has separate explicit approval; no additional exception is made here.
```

### SR-02 · not applied; specific human answer pending

```text
# Scope request SR-02: typed views of the two bundled constructors

Status: proposed, NOT applied. Automatic approval review rejected application.

The new generic-fuel harvest elaborates and has only the standard axioms, but
the full closure seals add nine diagnostics in its new proof. Eight arise from
the hidden tape/state fields of `ModuleHost.hostTM` and `IterateFind.copyTM`;
one needs an explicit local-budget simplification. The untouched original
`polyTimeComputable_find` independently has eleven baseline diagnostics. No
existing proof or definition is changed to hide any of those findings.

Prototype 3 validates the solution with both constructors still sealed. Prototypes
1 and 2 demonstrate why whole-machine equalities and raw run equalities alone
do not repair the dependent carrier types. Every source and raw log is retained.

## Exact proposed addition

`typed-views.patch` adds 84 lines to
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (672 → 756):

* `Turing.ModuleHost.hostTMView`, a reducible abbreviation whose explicit fields
  are `k := K`, `State := State C M`, and the original host's underlying machine;
* `hostTMView_eq` and `hostTMView_q₀`;
* `hostTMView_step_inl`, `host_call_view`, and `host_clean_view`, proved directly
  from the existing public contracts in the same file.

It adds 22 lines to
`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` (362 → 384):

* `Complexity.IterateFind.copyTMView`, with explicit one-tape, `Fin 2` fields;
* `copyTMView_eq` and `copy_clean_view`, reusing the existing copier contract.

Every existing declaration, definition, proof, and attribute remains byte-for-byte
unchanged. There is no transition-table copy, time-bound change, new admission,
or `simp` attribute. Both proposed files remain below 1000 lines and width 100.
The risk is expansion of the frozen shared-provider/rebuild scope; the purpose
is to remove implicit type-field reads in E1 while preserving all operational
seals. Header, clash, full-source seal, axiom, lint, and replay evidence would
cover both providers if approved.

## Authorization and automatic review

Seyoon delegated judgment over exceptions while away (see
`standing-discretion.txt`). The worker interpreted this as allowing these narrowly
necessary reader additions and attempted to apply/check them. Automatic approval
review rejected the action because it requires a specific scope approval for
these two provider files. No provider mutation occurred. The exact rejection is
in `automatic-review-rejection.txt`. Specific SR-02 approval is now requested;
independent final-consumer work continues in the meantime.

Answer: PENDING.
```

```text
Automatic approval review rejected applying/checking the typed provider views.
No command or provider mutation ran.

Verbatim reason:
This would modify two additional frozen provider files beyond the three pre-approved additions, but the brief requires a specific scope request to Seyoon for any such change and none authorizes these typed-view readers.
Do not bypass this rejection through a workaround or indirect execution. Continue with a safer alternative, or carry out checks to prove that the action is authorized or low risk before trying again. Complete unaffected work without asking for confirmation. Report anything that remains blocked, clarify why it was blocked by auto-review, inform the user of the risk and ask for approval.
```

No additional frozen-file mutation was made. The typed-view patch remains a proposal.

## Promotion and reader requests

E2/E3 are the issued pre-approvals and SR-01 is specifically approved. SR-02 is the
only further provider-reader proposal. No other promotion is included in this patch.

## Validation and evidence

* Both issued packs passed `shasum -a 256 -c`; their exact contents, checksums and
  logs are delivered under `evidence/verification/inputs/issued/` and `logs/`.
* Base and checkpoint each passed the complete 377-module supplied order. Every
  call checked one module via `scripts/lean_check_tree.sh`. No `lake build` ran.
* Base sorry audit: 26/12. Checkpoint audit: 25/12, with precisely the corollary removed.
* E1, E2, E3, SR-01, the original `polyTimeComputable_find`, and its consumer
  `polyTimeComputable_iterateFind` have only `propext`, `Classical.choice`, `Quot.sound`.
  All stored constants of the changed files were censused. The admitted targets'
  `sorryAx` behavior at this checkpoint is expected and stated above.
* Whole-file seals use actual full-import-closure Lean Names, both PolyExpr modes
  and strict/coe variants; raw catalogs, installation/EOF records, sources, line maps,
  and diagnostics are included. Invalid early harness attempts are retained separately.
* Header check and negative control pass. Whole-base clash scan: four additions,
  zero collisions. Explicit-unfold scan: zero added sites.
* Lint line-set diff: Cryptography remains 92 FAIL / 101 WARN; Complexity changes
  from 25 FAIL / 391 WARN to 25 FAIL / 390 WARN. There are no added FAIL lines.
  E3 removes the `DecidesInTime` reader warning. SR-01 removes `InBPP` from its
  missing-reader list; the inherited size warning changes 1403→1415 under the
  explicitly approved exception. Both changed WARN lines and all removals are listed.

## Host resources and execution exception EX-01

The host-wide cap is **at most three Lean processes total**, shared with other jobs.
Every Lean/Lake/check-tree command used the issued wrapper, `LEAN_SLOT_TAG=derand`,
and the default `~/.lean-slots`; cache commands used `-k 3`. Only narrowed roots were
fetched. The pinned Lean is 4.25.0 on arm64 macOS. Python ran as `python3 -I`.

The worker used its own proof and verification git worktrees and a separate delivery
worktree. Its physically owned pinned package tree is in the verification checkout;
the proof checkout links that same job-owned tree read-only. It shares no other
worker's package tree or TCSlib oleans. Each checkout has its own single-writer olean
tree. This execution arrangement is disclosed as EX-01 under the standing instruction.
The first evidence symlink was replaced with a physical evidence tree to satisfy
Lean's root-containment check; failed probe logs are retained.

The macOS preflights met the 4 GiB headroom and 12 GiB disk floors. No shortage,
exit 137/139, or jetsam event occurred. Long active modules and slot waits were
normal execution, not E-RES. Shared `~/.elan` and Mathlib archive-store provenance,
exact package pins, absent documentation-only packages, cache validation, and all
derand slot lines are recorded. Peer scheduling paused only the worker's Python
dispatchers at module boundaries; no native Lean or other worker was signaled.

## Commit reproduction and delivery

`patches/COMMITS.tsv` records author, committer, both dates and the signing column.
All commits use the configured checkout identity, with `commit.gpgsign=false`;
signing is `none`. Applying the complete patch series at the issue base in a separate
scratch clone reproduced every hash, ending at `776dabdabb276c75b98780e5018275fbcdc25e3a`. Raw reproduction commands,
metadata, expected hashes and actual hashes are in `evidence/reproduction/`.

The source branch is not pushed. This payload is delivered only under
`inbox/fills/derand/` from the worker's own delivery worktree; the delivery pulls with
rebase before its ordinary push. The exact delivered file set is checked against
the top-level `SHA256SUMS`, and the evidence has its own complete `SHA256SUMS`.
No other delivery path is edited. Maintainer review and Seyoon's PR approval remain
the landing process.
