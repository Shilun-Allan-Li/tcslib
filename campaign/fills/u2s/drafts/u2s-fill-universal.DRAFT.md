# Ch3–4 fill campaign — U2, the `k`-tape universal machine: U2-U and U2-E (`Turing.exists_selfUniversalK`, `Turing.universalK`, `UniversalK.lean`)

<!-- DRAFT (drafting agent), 2026-10-24, for megafill C. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (TCSlib as after #155; #156 open). Pre-ship measured
there, against a fresh bootstrap of the order list:
`campaign/fills/u2s/drafts/u2s-fill-universal/preship-77f1eb4f/`.
**Issue condition: the field-equation API PR Q-U1** (`campaign/fills/megafill/drafts/
megafill-C-DRAFTING-REPORT.md`): H2-F's encoding `Turing.StepBlock.forwardLoopCfg` and H5's
presentation `Turing.rulerHostCfg` are public definitions with no published lemma (the style
lint's check 8 lists both), and both phases' seams read their fields. This draft cites the
equations under the names `simps` generates beside them (`StepBlock.forwardLoopCfg_state`, …,
`rulerHostCfg_output`); at issue, replace them by the landed names if they differ, and re-run the
pre-ship against the API's head. Other issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩,
the megafill banner. -->

> **⟨Megafill C, item N⟩** (cover brief ⟨…⟩; addendum v2.5, Part 3). The preflight, the toolchain,
> the clone and the cache are done once for the whole queue. For this item: create its branch from
> the shared base (below), make your first edit, **re-bootstrap your order list**, then follow this
> brief. **Budget:** 4 hours (the cover's proposal) from your branch's creation. Deliver a
> checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your two targets as gated statements** (the U2 statement gate,
    `campaign/gates/26-u2-statements/`; `campaign/items/u2/U2-design.md` §2.2);
  - **the startup, proved** (PR #147, gate 63, PASS 0/0/4/15): `Turing.exists_selfStartupTMK` in
    your file, admission-free since the seam layout's landing (#145), with its `**Implementation.**`
    paragraph; its review `campaign/fills/u2s/reviews/startup-cont1/REVIEW.md` and the landing
    record `campaign/gates/63-u2s-startup-cont1-fill/`;
  - **H2-F, proved**: `Turing.StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward`), the
    forwarding round loop as a `Turing.Lockstep` through `Turing.StepBlock.forwardLoopCfg`, with
    its per-step bound and space ledger;
  - **H5, proved** (PR #146, gate 60): `Turing.exists_rulerHostTM` (`Build/InputDevice`), the
    bounded-prefix ruler host, a block simulation of any native-input machine on a suffix input,
    through `Turing.rulerHostCfg`;
  - **the field-equation API (Q-U1, ⟨its PR⟩)**: `StepBlock.forwardLoopCfg_state`, `_inputPos`,
    `_workTapes`, `_workTapePos`, `_output` and `rulerHostCfg_state`, `_inputPos`, `_workTapes`,
    `_workTapePos`, `_output`;
  - the lockstep API (`Build/Contract/Basic`): `Lockstep.runFrom`, `Lockstep.cut`,
    `Lockstep.locate` and the structure's fields;
  - the space API (PR #149): `MultiTapeTM.spaceUsed_eq_sum`, `MultiTapeTM.spaceUsed_le_of_abs_le`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**: Part 1, the resources and the cache for the Mathlib roots only, with the cache
    store logged first; **Part 3, the megafill**, under which this session runs), and the
    copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/u2s/inputs/u2s-fill-universal/`): the overlay
    `UniversalKOverlay.lean.txt` (your file with the one import of region (a)), the import probe,
    the route probe with its seal controls, and the screen population; the order list
    `campaign/fills/u2s/orders/u2s-fill-universal.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/u2s/logs/u2s-fill-universal-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/u2s-universal @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/UniversalK.lean
  # must print 4de5324eee700c701b0199f509084b26f77d5802
  # (the drafting base's blob, from git rev-parse; re-check at issue)
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-u2s-universal.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the session's shared environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-u2s-universal-cp<N>.zip` with the same contents as of that commit (the final sweep may be
  your module's check only). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip ⟨BASE⟩.** Lines in this brief are those of the
  drafting base's tree, where `UniversalK.lean` is #147's landing (1,762 lines; 12 public, 39
  private); re-check them at issue (the API PR does not touch your file).
- **Your first edit makes your file equal to the overlay** (`UniversalKOverlay.lean.txt`): the
  import of region (a) after line 11. **Line numbers below are the base's; the overlay's are 1
  more** (U2-U at 1716, overlay 1717; U2-E at 1754, overlay 1755).
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #156,
  `Build/Seam`'s `phaseHostTM_tr_of_red_none` and `phaseHostTM_run_le`, gate 69 pending: **not
  citable**; #135); on their own branches in this session, the other megafill items, among them
  **B5a** (`CodeSimulator`, upstream of your file through `Codes2Tape`; you cite nothing of it).
  Cite nothing they add.

## Parallel batches this round

None in `UniversalK.lean`. Your consumers: `Turing.exists_selfUniversal` (`SelfUniversal`, the
`k = 1` case of U2-U, already proved from your statement) and, through it, the space
hierarchy's `U₀`; U2-E is the code-first evaluator of `Turing.universal`'s U-1 retrofit
(deferred).

## What this is

**U2's two machine contracts** ([AB09, §1.4.1, Theorem 1.9; Exercise 4.1]). Two targets, frozen,
**one brief in two phases**: the targets share the startup and H2-F, but **neither follows from
the other**. U2-U runs the coded machine on its own input `pairEncode α w` through the native
input device; U2-E runs it on the suffix `x` of `pairEncode α x` through H5's ruler host, whose
host machine and time differ. So the order is: phase 1, U2-U; phase 2, U2-E, which reuses
phase 1's seam into H2-F.
1. **`Turing.exists_selfUniversalK`** (line 1716): one machine `U`; per code `α` a constant
   `C > 0`; on `pairEncode α w`, a halt of the coded machine with `output` within `t` gives `U`'s
   halt with `output` within `C · (t + 1)`, having visited at most `C · (s + 1)` cells (`s` the
   coded machine's by `t`), and every completed output of `U` is one of the coded machine's.
2. **`Turing.universalK`** (line 1754): one machine `U`; per code `α` a constant `C`; a halt of the
   coded machine on `x` with `output` within `t` gives `U`'s halt on `pairEncode α x` with
   `output` within `C · (t + 1)` (no `|x|` term), and every completed output of `U` on
   `pairEncode α x` is one of the coded machine's on `x`.

**The statements and their docstrings, frozen verbatim**: lines 1689–1725 and 1729–1760 at the
drafting base (blob above); the statements:

```lean
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  sorry

theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  sorry
```

Their docstrings' proof sketches (U2-U: (i)–(iv); U2-E: (i)–(iii)) bind where this brief does not
refine them.

**Where it stands.** Every host is proved: the startup ends at H2-F's encoding of the coded
machine's initial configuration (its docstring says so; the route probe derives it, below); H2-F
is a lockstep with a per-step bound and a space ledger; H5 hosts any machine on a suffix input.
What is open is the composition, the ledgers and the converses, and, for U2-E, the header ruler.

**Proved modulo, exactly:** none. The rows are admission-free (the import probe's five axiom
prints). **A complete delivery has no `sorryAx` in either target**, and then
`Turing.exists_selfUniversal` has none.

**Read first:**
- both targets' docstrings;
- `exists_selfStartupTMK`'s statement and `**Implementation.**` paragraph: its endpoint is the
  configuration your seam starts from, uniform in the suffix (`T`, `B` depend on `α` only);
- `StepBlock.exists_forwardLoopTM` and `Turing.Lockstep` with `Lockstep.runFrom`, `.cut`,
  `.locate`; `exists_rulerHostTM`;
- the route probe `U2UERouteProbe.lean.txt`: the seam premises of both phases, derived sealed
  against the API's equations; its proofs may be copied into your homes as `uk_` privates.

**Pre-ship check** (drafting agent, at the drafting base, the API stated as stand-ins; re-run at
issue against the API's landed names;
`campaign/fills/u2s/logs/u2s-fill-universal-preship.log`):
- **The overlay** elaborates with exactly the two targets' sorry warnings (overlay lines 1717,
  1755). The import creates no cycle, and `SelfUniversal`, the one downstream module that gains
  names through it, shares no declaration name with `Build/Rewind`.
- **The import probe** (`U2UEImportProbe.lean.txt`, a standalone import of your module and
  `Build/Rewind`, **77 checks of 77 names**, and five axiom prints): 0 errors, 0 warnings; the
  startup, H2-F, H5, `Lockstep.runFrom` and the work-tape rewind on the standard three axioms.
  **Re-run it after your delivery**, extended by the API's ten names and every further name you
  cite.
- **The route probe** (`U2UERouteProbe.lean.txt`), sealed over 8 TCSlib definitions (the two
  `@[simp]` ones, `MultiTapeTM.initCfg` and `Cfg.init`, also erased), with the API's equations as
  `rfl` stand-ins proved before the seal: 0 diagnostics. `u2_encode_init_tapes` and
  `u2_encode_init_fields` (the startup's endpoint on the first `k + 2` tapes is
  `forwardLoopCfg entry M (M.initCfg _)`), `u2_encode_halt` (the encoding halts exactly when the
  source does, with its output), `u2_ruler_fields` (the host's presentation).
- **The seal controls** (`U2UESealControl.lean.txt`, 8 `rfl` goals): every one closes unsealed and
  fails sealed; the first two are the API gap.

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target | Phase |
|---|---|---|---|
| 1 | `UniversalK.lean:1716` | `Turing.exists_selfUniversalK` (frozen statement) | 1 |
| 2 | `UniversalK.lean:1754` | `Turing.universalK` (frozen statement) | 2 |

Your regions:
- **(a) the import**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.Rewind`, after line 11 (the overlay). No other
  import.
- **(b) U2-U's home**, the blank line 1688, between the section header
  `/-! ## U2-U: the self-application universal machine -/` (1687) and U2-U's docstring (1689):
  your phase-1 `private` declarations, the seam into H2-F first (phase 2 reuses it).
- **(c) U2-E's home**, the blank line 1728, between `/-! ## U2-E: the code-first evaluator -/`
  (1727) and U2-E's docstring (1729): your phase-2 `private` declarations.
- **(d) the two bodies**, the `sorry`s on lines 1725 and 1760.
- **(e) for an open target only, a paragraph headed `**Implementation status.**`** at the end of its
  docstring, before the closing ` -/` (1715, 1753). It is public-facing library text: what is proved
  and what is open, in mathematical terms, with no campaign labels, no dates and no session
  narrative. The same holds for your new docstrings; provenance goes in `REPORT.md`. **Every new
  declaration has a docstring, and every proof over 20 lines a literal `**Proof sketch.**`
  paragraph** (`policy.md` §3; the canonizer's and the seam layout's landings each needed a
  follow-up PR for missing ones).

In (b) and (c): `private` only, and no `section`, `open` or `variable` that leaks past one
(`open … in` on one declaration is fine). Frozen: the module header and status text (lines
29–32: the maintainer updates them at integration), the scheme interface, U2-S's section (the
startup and its 39 `ss_` privates: cite the startup's statement only), both statements and their
docstrings before (e), and every other file.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The loop:** H2-F, `StepBlock.exists_forwardLoopTM k`, through its lockstep. **Never write a
  second step block, round loop or forwarding leaf.**
- **The suffix device (phase 2):** H5, `exists_rulerHostTM`. **Never write a second input
  device.**
- **Compose by the public combinators:** R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`,
  `seamCompTM_firstReturn_ofCfg`, `seamCompTM_runFrom_left`/`_right`,
  `seamCompTM_visitedByTapeHead_ofCfg`), the phase host (`phaseHostTM`, `phaseHostTM_run`), R1
  (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_eq`, `embedEmitTM_visitedByTapeHead`,
  `_frame`): both H2-F's loop and H5's host emit, so embed them by R1, not R1′.
- **Leaves you may write: one, phase 2's header-ruler scan** (below), with a docstring saying no
  public row writes a ruler of the header's length. It is a leaf (a finite-state scan), not a
  host. Any further leaf is an escalation.
- **Promotion candidates** (notes only, in `REPORT.md`): the seam into H2-F
  (`exists_selfUniversal`'s `k = 1` case and `Complexity.space_universal` reuse it), and the
  header-ruler scan (whose second consumer is `Complexity.space_universal`'s startup).

### The route (binding where it names a row)

Write `M := E.machine α`, `c₀ := M.initCfg z` (`z` the simulated input), `L`, `entry`, `C_L`,
`cost` from `exists_forwardLoopTM k`, and `R`, `exit`, `T`, `B` from `exists_selfStartupTMK k E`.

**Phase 1, U2-U** (checkpoints 1.1–1.5).
1. **The seam into H2-F** (checkpoint 1.1). `U` is the startup `R`, seamed at its `exit`
   (`seamCompTM`) into the embedded `L` (R1 on the first `k + 2` of `R`'s `K + (k + 2)` tapes: tape
   `j` of `L` is tape `⟨j, _⟩` of `R`). At `R`'s exit, the embedded part of the configuration is
   **`forwardLoopCfg entry M c₀`**: `uk_encode_init_tapes`/`uk_encode_init_fields` (the probe's
   `u2_encode_init_*`, through the API's `forwardLoopCfg_workTapes`, `_workTapePos`, `_state`,
   `_inputPos`, `_output`, `MultiTapeTM.initCfg_eq`, `Cfg.init_*`, `Fin.addCases_left`/`_right`,
   `StepBlock.summaryCells_eq`, `FinTM.bufferTape_of_neg`). The other `K` tapes are blank, every
   head at `0`, by the startup's endpoint.
2. **The forward ledger** (checkpoint 1.2). If the coded machine halts on `z` with `output` within
   `t`, let `t₀ ≤ t` be its first halting time (`MultiTapeTM.exists_first_halt`, or the least such
   time). `Lockstep.runFrom` at `t₀` gives `L` at `forwardLoopCfg entry M (M.runFrom c₀ t₀)` after
   `Σ_{u < t₀} cost (M.runFrom c₀ u)` steps; `uk_encode_halt` (the probe's `u2_encode_halt`):
   halted, with `output`. Each cost is at most `50 (|tableBitsK M.tr| + 1) + C_L`. So `U` halts with
   `output` by `T + 1 + t₀ · (50 (|tableBitsK M.tr| + 1) + C_L) ≤ C · (t + 1)` with
   `C := T + 1 + 50 (|tableBitsK M.tr| + 1) + C_L` (per code), and `ComputesInTime.mono`.
3. **The space ledger** (checkpoint 1.3). `U`'s space to `C · (t + 1)` is its space to its halt
   (a halted run is frozen: `MultiTapeTM.runFrom_of_halt`), the startup's at most `B`, plus the
   embedded `L`'s by tape (`spaceUsed_eq_sum`, `seamCompTM_visitedByTapeHead_ofCfg`,
   `embedEmitTM_visitedByTapeHead` and `_frame`): H2-F's ledger puts each mirrored tape's visits
   inside `M`'s (at most `s` in all) and each auxiliary head within
   `50 (|tableBitsK M.tr| + 1) + C_L` of home. The total is at most `C · (s + 1)` after enlarging
   `C` by those per-code terms.
4. **The converse** (checkpoint 1.4). If `U` halts with `output` at some `t'`, `L` halted by then
   (`R` and the seam are live before the embedded halt); if `M` were live before every time, the
   lockstep's cut (`Lockstep.cut`) and `cost ≥ 1` on live configurations would keep `L` live past
   every bound. So `M` halts at some `t₀`, and `L`'s halted configuration, by determinism, is
   `forwardLoopCfg entry M (M.runFrom c₀ t₀)`, whose output is `M`'s (`uk_encode_halt`).
5. **U2-U proved** (checkpoint 1.5), with `0 < C`.

**Phase 2, U2-E** (checkpoints 2.1–2.5), on `z := pairEncode α x`, with `ℓ := 2|α| + 2`, the
header's length (`length_pairEncode`, `universal_pair_length`), and `z.drop ℓ = x`.
1. **The header ruler** (checkpoint 2.1): the startup on `z` (its endpoint is uniform in the
   suffix, so `w := x`), then **the authorized leaf**: from input position `1`, read the header in
   aligned pairs, writing `true` on a blank ruler tape for each header cell, and stop at the
   separator pair `[false, true]` with the native head at `ℓ + 1` (virtual position `1`). Its run
   lemma: exact time `ℓ + O(1)`, the ruler `FinTM.bufferTape (List.replicate ℓ true)` from its
   start, every other tape and head unchanged, silent. **`α = []` is allowed** (`ℓ = 2`). Then
   the ruler's **rewind** by `rewindTM_run_ofCfg` at `n = ℓ`: its head at the ruler's first cell,
   which is `exists_rulerHostTM`'s ruler hypothesis (`rt (rp + p) = bufferTape (replicate ℓ true) p`
   for `-1 ≤ p ≤ ℓ`).
2. **The host's start** (checkpoint 2.2): `H` from `exists_rulerHostTM L` (on `(k + 2) + 1` tapes,
   the ruler last, `inj`, `C_R`). The configuration after step 1, on `L`'s tapes and the ruler, is
   `rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c rt rp` with `c := forwardLoopCfg entry M
   (M.initCfg x)`: `uk_ruler_fields` (the probe's `u2_ruler_fields`, through the API's
   `rulerHostCfg_*`) and phase 1's `uk_encode_init_*` at `x`. **The tag is `false`**: `c`'s input
   position is `1`, not `0` (`b = true ↔ c.inputPos.val = 0`).
3. **The forward ledger** (checkpoint 2.3): `L` reaches the encoded halt at
   `t_L := Σ_{u < t₀} cost (M.runFrom (M.initCfg x) u)` (phase 1, step 2); `exists_rulerHostTM` at
   `t_L` gives `H` at the presentation of that configuration after `t' ≤ C_R (ℓ + 1) t_L` steps,
   halted with `output`. The total
   `T + (ℓ + O(1)) + (ℓ + 2) + seams + C_R (ℓ + 1) t₀ (50 (|tableBitsK M.tr| + 1) + C_L)` is at most
   `C · (t + 1)` per code, **with no `|x|` term** (the startup and the ruler depend on `α` only).
4. **The converse** (checkpoint 2.4): `H`'s cut (live before `t'` when `L` is live before `t_L`)
   and `t ≤ t'`, then phase 1's converse argument for `L`.
5. **U2-E proved** (checkpoint 2.5).

**Edge cases that must stay true:** `k = 0` (the table and summary are tapes `0` and `1`); an empty
suffix `w = []` or `x = []`; `α = []`; a canonizer with no work tapes; an arbitrary
`E.canonizerTime`; a coded machine that never halts (the converse).

## Gate guidance (binding)

- **The U2 statement gate:** the control varies with `k` (and `E`) alone; `T`, `B` and `C` may
  depend on `α`; no `|x|` term in U2-E's bound; the converse clauses are binding (divergence is
  preserved).
- **Gate 63** (the startup's landing): cite the startup's statement as it is; its
  `**Implementation.**` paragraph describes the construction.
- **Gate 60** (H5's landing) and its resolutions' C60-1/C60-2: the ruler host's exits are return
  points; cite `exists_rulerHostTM` as stated.

## Cited infrastructure (public and proved at the issue commit; all in `U2UEImportProbe.lean.txt`)

The probe's 77 names (the targets, the scheme and the startup; H2-F and the lockstep; H5 and the
header's length; the rewind; a leaf's one-step lemmas; composition, embedding and their visited
sets; runs, outputs and space), and the API's ten field equations.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(e) of `UniversalK.lean`. List every new
   declaration with its role.
2. **Statement freeze** over both targets and every landed public declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. Phase 2 does not depend on phase 1's ledgers or converse, only on its seam (1.1).
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the one in region (a).
7. **One proof per shared argument.** Never write a second host, loop, seam, embedding, prefix
   parser, layout machine or input rewind; never re-walk U2-S's `ss_` privates or `SeamLayout`'s,
   `InputDevice`'s or `StepBlockForward`'s privates. The header-ruler leaf is allowed.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 1,762 lines; 12 public, 39 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and both targets' axiom walks. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either. Read
      `forwardLoopCfg` and `rulerHostCfg` only through the API's field equations; `Lockstep`
      through its fields and `runFrom`/`cut`/`locate`; the startup through its statement;
      `MultiTapeTM.spaceUsed` through `spaceUsed_eq_sum` (never by its definition).
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas (`Bool.toNat_true`, not `simp [Bool.toNat]`;
      `Fin.addCases_left`, not `unfold Fin.addCases`).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file (the header-ruler scan).
    - Your own file's definitions may be unfolded (`EffectiveCodeK.toFinTM`, your `uk_`
      declarations).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your proofs mention (start from the pre-ship's 8 and
        extend: at least `Lockstep`'s consumers' definitions you reach, `seamCompTM`,
        `embedEmitTM`, `MultiTapeTM.runFrom`, `MultiTapeTM.spaceUsed`, `rewindTM`), and
        `attribute [-simp]` on the `@[simp]` definitions among them, which must still elaborate,
        **with controls**: for each sealed definition, a goal that closes by `rfl` with nothing
        sealed and fails under the seal;
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure.**
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep your new privates under the `uk_` prefix (unused in the tree at the
    drafting base).

### Checkpoints (for a partial; ground rule 9)

1.1–1.5 then 2.1–2.5 above. Each may land alone. **Add no new admission:** a helper is inserted
only once proved. The freeze check for a partial is the axiom walk: `sorryAx` reaches each target
only through its own open body.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen after your first edit: it must equal the screen base (the overlay changes only an import).
- **The population** is 20 files
  (`campaign/fills/u2s/inputs/u2s-fill-universal/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/StepBlockForward`, `Build/Contract/Basic`,
    `Build/InputDevice`, `Build/StepBlock`, `Build/Seam`, `Build/Embed`, `Build/Rewind`,
    `Build/Catalog`, `Deterministic`, `Finite`;
  - the known hazards: `SelfUniversal`, `SpaceComplexity/Hierarchy` (`space_universal`'s
    code-first startup), the chapter-1 universal machine (`Universal`,
    `UniversalInterpreter`, `UniversalStartup`), the interpreter core (`NDCodeSimulator`), Z1
    (`Build/VirtualInput`), H2's clocked form (`Build/StepBlockLoop`), and `Simulation` (the input
    rewind family; this item writes none, but its startup sits beside U2-S's `ss_inputRewind`).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/u2s/logs/u2s-fill-universal-screen-base.txt`: **1,039
  declarations, 785 pairs, 213,552 characters** (MEASURED at the drafting base; about 10 minutes).
  14 pairs have a declaration of your file on one side: 13 within it (none at 90% or more), and
  one across files (`ss_inputRewind_run` of `Universal`'s `timedFrame_run`, 56%).

```sh
P=campaign/fills/u2s/inputs/u2s-fill-universal
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:** H2-F's and H5's private proofs (`fl_*`, `rd_*`: cite their contracts);
  the chapter-1 universal machine's code-first startup and its boundary marker
  (`UniversalInterpreter`); `SelfUniversal`'s corollary; the lockstep-transport family
  (`Contract.lockstep`, Z1's `vhostEmitTM_runFrom`: cite `Lockstep.runFrom`); the
  `Cfg.mapState_mapState` field-equation idiom (two accepted idiom pairs: say so if yours is a
  third). A pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification (phase 2's reuse of phase 1's seam is
  a citation, not a copy). Quote both outputs in `REPORT.md`, which carries **"new copies: none"**
  (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for the queue's Mathlib roots only** (addendum v2.5,
  fetched once at the session's start; your order list's modules import 40 roots directly);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Re-bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/u2s/orders/u2s-fill-universal.txt` (**96 modules**, computed on the overlay; the
  same set as the base's), after your first edit, logging each module's start and end time and
  maximum memory. **The base sorry-warning set has 27 entries in 12 modules**
  (`campaign/fills/u2s/logs/u2s-fill-universal-base-sorries.txt`). Yours are `UniversalK`'s two.
  Record the base list by name first, and report any difference.
- **Final checks:**
  1. `UniversalK`: zero errors, no sorry warning (for a partial, exactly the open targets'), and
     no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (25 for a complete delivery).
  3. Re-run `U2UEImportProbe.lean.txt` (extended by the API's names and your citations): 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for both
  targets and every new private, and for `Turing.exists_selfUniversal` (in a probe importing
  `SelfUniversal`): within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete
  delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 68 WARN over 83 files; `UniversalK`'s are its size and two public definitions
  without a lemma, `EffectiveCodeK.ofSerialize`, `EffectiveCodeK.toFinTM`). No new line over 100
  characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your two targets: MIG-1 stage S's sorried specs
(`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop`, `Build/Primitives`); `Build/RecordTable`'s four rows; `Build/ZoneRebalance`'s two;
`CodeSimulator`'s `exists_uniformSimulator`; `NDCodeSimulator`'s `exists_replayCanonizer`. If a
proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs, the cache store's
      log included), **the shared logs copied into this zip**, this item's bootstrap with
      per-module time and memory, and the base blob check.
- [ ] The overlay as the first edit; nothing else outside regions (b)–(e).
- [ ] The checkpoints reached; the base hash and the ancestor check; the checkpoint zips written.
- [ ] Every new declaration with its role; the tapes of each machine (the embedding of `L`, the
      ruler tape); the header-ruler leaf and its run; the status paragraphs, if partial.
- [ ] `C` for each target, term by term; the space ledger's terms.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs**, and the inspection table. Rule 11: a grep of your diff for the six R3 rows and for
      other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints (both targets and `exists_selfUniversal`);
      the lint line. The diff touches only your owned regions.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `Cfg.mapState_*`,
  `embedEmitCfg_*`, and the API's): `funext` before `rw`, or the step closes by unfolding and the
  seal rejects it (the route probe needed it at `Cfg.init_workTapes`).
- **The startup's summary tape is `fun p => bufferTape (unaryFin q₀) (p - 2)`**, the encoding's is
  `StepBlock.summaryCells none (unaryFin q₀)`; they agree at every cell, cell `0` by
  `FinTM.bufferTape_of_neg` (`StepBlock.summaryCells_eq`; the probe's `u2_encode_init_tapes`).
- **`Fin.addCases` splits `Fin (k + 2)`** as `Fin.castAdd 2 i` (the mirrored tapes) and
  `Fin.natAdd k j` (`j = 0` the table, `j = 1` the summary): `Fin.addCases_left`/`_right`,
  `Fin.coe_castAdd`, `Fin.coe_natAdd`.
- **The ruler host's tag** is `true` exactly at virtual position `0`; H2-F's encoding of an initial
  configuration is at position `1`, so the start tag is `false`.
- **`exists_rulerHostTM` needs `0 < ℓ`** and the ruler's two blank delimiters (`p = -1` and
  `p = ℓ`); `ℓ = 2|α| + 2 ≥ 2`.
- **H2-F's `cost` is chosen per source configuration** (`exists_forwardLoopTM`'s `∃ cost`), after
  `M`: the time ledger sums it along the run, bounded per step.
- **A halted run is frozen** (`MultiTapeTM.runFrom_of_halt`): `ComputesInTime` at `C · (t + 1)`
  follows from the halt at the first halting time by `ComputesInTime.mono`, and the space to
  `C · (t + 1)` is the space to the halt.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
