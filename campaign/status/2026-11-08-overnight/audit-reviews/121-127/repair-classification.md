# Exact repair classification for returned gates121/127

All proposals below are source inspection only. No Lean/source/records edit or test was performed in this return review. Source is immutable gate121 `d64dff4fbef865d815c6a561ce8037ea1bae07a2`, gate127 `e16049ad20823b3e6abba171e328489746062080`; MAC8 BASE is `9b5dcf46408db681bcbc721930ef2203fa6bc47d`.

## Gate121 major1: confirmed, still open

The five donor proofs are authored source instances of a direct `MultiTapeTM.step` read. The `unfold MultiTapeTM.step; rw [hc]` prefixes occur at Hardness1703/2963/3382/3426/3782. `Deterministic.lean:200–203` already publishes exactly that equation as `step_of_some`. Replace each two-line prefix by `rw [MultiTapeTM.step_of_some hc]`, then retain/review the existing own transition-table reduction and `FinTM.controlAction_apply`/`moveInputPos_zero` tail. The five complete headers, names, imports and machine definitions stay exact. This is an existing-reader repair; no new design decision is identified for these five prefixes. It is not yet a native/full-seal result.

The complete five-owner raw census is uncapped in `uncapped-five-owner-step-census.json`: Hardness58 and EXP32 raw closing lines; XR/InputCall/InputLength0 for this line-level pattern. Twelve Hardness `_idle` proofs explicitly read `step`; the five above plus clCount1080, clBank1231, clRow2124, clLoad3641, clPrepare3883, clPrepared4847, clRecord4991. Include these seven companions in the same-kind inspection. Some also explicitly name Action.apply/controlAction or other foreign definitions, so changing their first line alone is not a full repair. The other raw operational simulation/dispatch lines require distinct per-site review;90 raw lines are neither90 unique copies nor a proof of semantic exhaustiveness.

FE-LIVE-1 acknowledges first selection of a whole-configuration fixed live stop, including positive-time/predicate/inline forms. It does not authorize every operational definition read used to prove the fixed-point premise. The seven SG1 kinds likewise supply no blanket rule10 exception. Old restored source and an accurately labeled HOLD are disclosure, not human retention approval. The audit's governance major is therefore valid without a mathematical counterexample or a new one-fifth crossing.

## Held comparator: existing-reader candidate before any new API

Current complete target is Hardness7184–7265. Preserve its exact statement, output bit and35*(arg.length+1) bound. The following local repairs can be attempted without a new public API/import:

1. Replace `Cfg.ofWords ... := rfl` by its already-imported five field equations using Cfg.ext. The isolated generic full-field example18 passed with ofWords hidden. This is not a full comparator pass.
2. The comparator contract does not require positive t. The old `hp` obtained from clFirst is unused. Select t directly with `MultiTapeTM.exists_first_entry_of_fixed`, stop predicate `fun q => ∃ v : Bool, q = ret v`, current full `hend`, and the existing `idle v cfg hc` for each verdict. Obtain resultState through own clPreparedCfg and existing clPlacedCfg_eq. Then `hcut j hj ⟨ret v, hv, v, rfl⟩` supplies the complete guard. This removes both the seamCompTM-dependent initial-state exclusion and the old add/iterate-fixed guard reproof. It requires no seamCompTM q₀ reader or positivity statement change. The route is proposed, unexecuted.
3. Keep local `actionid`, reconstruct Action by its four published mapState field equations. The correct historical sealed16 snippet handles the workTapes function by funext and ends with rfl; failed03/15 are not passing evidence.
4. Keep local `mapid`, use Cfg.ext and the five already-imported StateRenaming field equations plus Option.map_id/rfl/funext. **Do not paste sealed21's CfgFacts version into Hardness unchanged:** the exact current import graph has StateRenaming via Seam but does not contain CfgFacts. Adding CfgFacts would be a new import decision. The field-reader version avoids that decision. Historical isolated21 is only supporting evidence in its own import context.
5. Finish the emitting step through `step_of_some` and Action.apply's five field equations, Cfg.workTapeSymbols_eq, moveInputPos_zero and output-field equality. The old explicit `simp [Action.apply]` and foreign definitional `change` must not remain hidden behind a narrow first-entry seal.

Check all implicit `change`/`rfl` conversions as well as explicit arguments throughout this complete target. The prior full17-head guard stopped first at ofWords, before these later obligations; no pass of the whole comparator is currently established. This existing-API candidate should be tried before treating a new seam API as necessary. If another reader/import/header/API decision becomes necessary, stop only that front and present that precise decision; do not grant retention.

## InputLength: direct field repair plus a real full-scope boundary

At InputLength500–501, replace `simp [c, inputLengthCfg, Cfg.inputSymbol]` with `exact Cfg.inputSymbol_of_end rfl` (or apply plus rfl). Configuration213 publishes the exact endpoint-reader contract. No import/header/definition change is needed. Historical native19 passed that private candidate; it also included the older held first-entry transform, so it is not an executed check of a newly edited actual owner.

Historical complete sealed20 still fails later in both input cases of the `.returnScan` transition premise to FinTM.rewind_heads: the owned transition table calls foreign `inputFoldTM ... .bwd ()`. Build/Scan535–548 defines that foreign row, and the1003-source named-reader search finds no published/generated tr equation. Public inputFoldTM_run_ofCfg645 is an initialized forward-run contract, not this arbitrary backward-phase transition premise. Thus the direct endSymbol repair is not a certified complete InputLength fix.

A minimal *pending* public-contract proposal, only if no existing larger contract removes that read, is the following non-simp equation beside inputFoldTM in Build/Scan:

```lean
theorem inputFoldTM_tr_bwd {Γ : Type*} {A : Type} (k : ℕ)
    (δ : A → Γ → A) (a₀ a : A) (inp : Option Γ)
    (work : Fin k → Option Γ) :
    (inputFoldTM k δ a₀).tr (.bwd a) inp work =
      (match inp with
       | some _ => inputMoveAction (-1) (.bwd a)
       | none => inputMoveAction 1 (.done a)) := by
  rfl
```

This is a concrete proposed reading, not an approved new declaration or a tested skeleton. Scan is already in InputLength's import closure. The new public API/frozen source decision belongs to Seyoon; no import/home/route/debt permission is inferred. A new equation alone is not claimed to settle all Action.mapState/inputMoveAction field obligations. Retention instead of repair requires its own exact kind/owner/window ruling.

## Records-only repairs

Gate121 minor2: add the original four `MANIFEST.json` / `SHA256SUMS.txt` files for compact-census and nine-boundary to the portable list, preserving their exact bytes and the old817 publication as historical. All78/176 payload entries reconcile against the total path map; no validation payload was lost. Adding only these four would yield821 selected sections, but a real source-fix reissue will have its own complete inputs/count/hash. Do not relabel817 as complete for these four.

Gate127 minor1: change reproduction-tools/context.json's replay_helper value from `review/replay/leanelab-o.sh is self-contained` to `review/replay/drivers/leanelab-o.sh is self-contained`. At the pinned records commit the first path is absent and the second is bundled/verified. This correction changes context records, not CodeSimulator, its metadata, replay or screen evidence.

## Scope after edits

Root should preserve both audit returns verbatim with their intake hashes, give a disposition per finding, bind source patches/header freezes/current exact evidence, add the integrity files, and correct the127 pointer. New source changes need the repository's complete-scope native/seal/control/type/AX/sourceQA/replay/screen checks as appropriate to the actual final scope and current source context. Existing execution pins remain historical; do not imply fresh checks or automatic validity after unrelated source merges. This read-only review does not authorize running those checks.

Gate121 remains HOLD until its major is repaired or Seyoon gives a precisely scoped ruling. Gate127's minor is suitable for a records correction and root disposition; the audit PASS is not merge clearance. All eight source PRs remain unmerged. Any follow-up auditor selection must be obtained for that item unless Seyoon explicitly supplies it; the morning Codex batch does not silently select later rounds. No gate closure/dispatch/merge is performed here.
