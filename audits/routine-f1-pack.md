# External audit pack — machine-routine layer (§12), epoch F1 fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4c), the
§12 fill campaign's first epoch. The statement gate closed in three rounds
(`audits/routine-infra-resolutions.md`); this round audits the **fills**:
37 of the 56 audited-true statements proved by three parallel batch agents
(plan §4c: F1A `Build/Embed.lean` 13/13, F1B `Build/Seam.lean` 11/11,
F1C `Build/Catalog.lean` Part 1 + W1/W2 13/13). Epoch gates follow the
statement-gate rule: the gate closes on a round with zero blockers and zero
majors (`workflow.md` §4).

Audited at commit `bf1b6d04` (branch `complexity/arora-barak-ch3-4`). The
fills are the three attached patch series (Codex-authored, integrated by
`git am -3` as `d20ab758`, `a5012741`, `2f67e910`); the agents' own
`REPORT.md`s are attached verbatim. **Every proof is kernel-checked** — the
maintainer's replay evidence is below — so this audit's object is not
correctness of the checked terms but the **surface**: the sixty new private
declarations (A 14, B 13, C 33 — blind-restate each against its role), the
honesty of the helper statements (a vacuous or subtly weakened private
lemma misleads every later fill that imitates it), fidelity of the proofs
to the binding inherited contracts, and the handful of declared anomalies
below.

## Brief for the auditor

1. **Blind-restate all sixty new private declarations** from their bodies
   (the reports' role tables are claims to check, not ground truth): A's
   `embedSlot_selected`/`embedSlot_unselected` glue pair, the four
   `*_apply`/`*_step` transports, the `embedReturn*` encodings and
   `embedThroughHalt` core, `embedReturn_visited`; B's `seamComp_step_*`,
   `seam_stationary_apply`, `seamComp_dispatch`, the `seamComp_left`/
   `seamComp_right` lockstep identities (they must be exactly the round-2
   report's two displayed full-configuration identities), the general
   cores, `seam_ofWords_mapState`; C's `catalogCfg`/`catalogTrace`
   configuration-trace family and the per-routine invariants.
2. **Check contract fidelity**: A's returning-run proofs against the
   round-3 five-step plan (positive time; component check; live-prefix
   induction; last step; first-visit exclusion) and the visited equalities
   proved **without** the through-halt contracts (the binding independence);
   B's canonical theorems derived as instances of the general cores with
   **no independent lockstep proof** and the visited containment with **no
   phase-two endpoint hypothesis**; C's budgets landing on the exact
   movement table (`2L+2`, `2d+2`, `2p+2`; intervals `[-1,·]`), W1's
   per-prefix `capture_run` application including the terminal emission,
   W2's trajectory agreement with no output or termination hypothesis.
3. **Assess the declared anomalies**: (i) A's two unused-`hcap` warnings —
   the frozen signatures keep the hypothesis while the private transports
   hold without it; is the exported capture interpretation still the one
   the statement advertises, and is keeping the premise the right call?
   (ii) A's two flagged **Fill appendix** docstring additions — appendices
   only, no audited sketch text altered? (iii) C's requested shared lemma
   (a public `redirectTM` head-trajectory projection) — right shape for
   the natural-home queue? (iv) The three deliveries' environment-shim C
   files were **excluded** (not compiled, not run, not integrated,
   unreferenced by the patches) — flag if any integrated artifact
   nonetheless depends on anything outside the Lean sources.
4. Report anything the fills newly misstate — in the standard table and
   severity scale. Statement bodies were frozen; verify no signature,
   definition, or F2-row drift against the attached patches (the
   maintainer's mechanical check found removals only at `sorry` bodies).

## Repository-side attestations (verify or challenge)

* Freeze (maintainer, mechanical): across all three patches, every removed
  line is a `sorry` body except A's two flagged appendix re-terminations;
  each patch touches only its owned file; C's 19 epoch-F2 statements remain
  sorried and byte-identical.
* Fresh replay (`audits/logs/routine-f1-integration-sweep.log`, revision
  recorded at start: `bf1b6d04`'s parent set, re-run post-integration):
  the three modules plus the `TuringMachine` facade, 0 `error:` lines,
  fresh `.olean`s, **exactly 19** `declaration uses 'sorry'` warnings, all
  in `Catalog.lean`'s F2 rows. `Embed.lean` and `Seam.lean` are
  **zero-sorry**.
* Independent axiom prints (`audits/logs/routine-f1-axioms.log`, generated
  by the maintainer, not the agents): all **37** filled theorems at most
  `[propext, Classical.choice, Quot.sound]` (several proper subsets);
  `sorryAx` appears nowhere.
* Style lint (`audits/logs/routine-f1-stylelint.log`): 0 FAIL;
  size WARNs only (Catalog now 1851 lines — the queued per-theme split,
  backlog §2 decision 12.2(c), is the recorded justification; Embed 931
  and Seam 696 exceed the 600 target as INFO).
* Delivery integrity: `SHA256SUMS` verified 15/12/14 files OK; each zip's
  bundle verifies against its recorded base `42d524b6`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/routine-f1-findings.md`; the epoch gate closes on zero blockers and
majors, after which epoch F2 (the 19 Catalog space rows) dispatches.
