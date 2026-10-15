# Retrofit RB1 report

**Complete: both binding tasks landed in two checked commits.** No task escalations or unfinished frontier. No push, pull request, or rebase was performed.

## Base and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `5588628cbbddea9546f616907364b608e15557fd`.
- Working branch: `fill/retrofit-rb1`.
- Final commit: `2bb8f379e1560dbdf6c693c1a1f40f417297876f`.
- Brief-issued base: `ff012d28ca3131452161669e1d7efe389b75ba2e`. The owned file was byte-identical between that commit and the recorded base.
- The complete Git diff touches only `TCSlib/Complexity/TuringMachine/Build/Loop.lean`. The archive's `Loop.lean` is that full modified source file.

| Commit | Task | Result |
|---|---|---|
| `cccc46916d79f9dffbf3d27a2ad3f40e2e09c8e0` | Delete eight dead declarations and update the historical sentence | Fresh Loop check: 0 errors, 0 sorry warnings |
| `2bb8f379e1560dbdf6c693c1a1f40f417297876f` | Derive body forwarding from public `emit_run` | Fresh Loop check: 0 errors, 0 sorry warnings |

Each commit was created only after its successful fresh Loop check. Immediately after each commit, the committed blob and working file were verified byte-identical to the checked source. `commit-checks.log` records those checks and source hashes. The final committed version was then compiled afresh again in the final sweep.

## Task 1: completed

All eight declarations, together with their docstrings, were removed:

| Declaration | Disposition |
|---|---|
| `loop_silent_prefix` | Deleted |
| `loopDebitTM` | Deleted |
| `loopDebitCfg` | Deleted |
| `loopBorrow_step` | Deleted |
| `loopBorrow_run` | Deleted |
| `loopBorrow_rewind` | Deleted |
| `loopBorrow_correct` | Deleted |
| `loopBody_capture` | Deleted |

The post-deletion compile succeeded; no missed referencer was found and no declaration needed restoration.

The one historical sentence formerly referencing `loopBorrow_correct` now reads:

> The host performs the counter borrow and rewind in phases 8--10.

Every other byte of that docstring was retained.

## Task 2: completed

Removed `emLoop_forward_apply` and `emLoop_forward_run`, including their docstrings. Retained `emLoopForwardCfg` and its docstring byte-for-byte: the existing call representation and frame proofs still use that configuration definition. The local forwarding proof family is replaced by a direct `Turing.emit_run` citation inside its sole proof consumer, `emLoopHost_body_forward`.

The replacement follows the binding glue plan:

1. `padded` is a local machine extending `loopBodySource` by one inactive tape through `leftAction 1 id`.
2. Local fact `hrun` is a direct `leftCfg_run` application and supplies both the padded trajectory and its liveness guard.
3. Local fact `hcfg` uses one `Cfg.ext` to commute `emitCfg` with `leftCfg`.
4. Simplification, including `Option.map_id`, proves the host agreement by commuting `emitAction` with the padding action.
5. `Turing.emit_run` supplies the guarded forwarding run, including any emission on the source's final halting transition.

**New private declarations: none.** `src` and `padded` are local bindings; `hrun` and `hcfg` are local proof facts, with the roles above. No private declaration was renamed or re-signatured. The consumer's statement and docstring are unchanged. Its new proof body is:

```lean
  -- Pad the stopped body, then use the public forwarding contract in this host.
  let src := loopBodySource body F anchor
  let padded : MultiTapeTM (body.k + 1 + (1 + F.k) + 1) Bool (body.State × Bool) :=
    ⟨src.q₀, fun q inp work => leftAction 1 id (src.tr q inp (fun i => work i.castSucc))⟩
  have hrun (u : ℕ) := leftCfg_run src padded id (fun _ _ _ => rfl)
    c (fun _ : Fin 1 => bufferTape []) (fun _ => 0) u
  have hcfg (emb : body.State × Bool → LoopHostState body F) (ret : LoopHostState body F)
      (d : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) :
      Turing.emitCfg emb ret pre (leftCfg id d (fun _ : Fin 1 => bufferTape []) (fun _ => 0)) =
        emLoopForwardCfg emb ret pre d := by
    refine Cfg.ext ?_ rfl rfl rfl rfl
    simp [Turing.emitCfg, emLoopForwardCfg, leftCfg]
  rw [← hcfg]
  rw [Turing.emit_run padded _ _ _ ?_ pre _ t ?_, hrun t, hcfg]
  · intro q inp work
    simp [padded, src, emLoopHost, Turing.emitAction, leftAction, Option.map_id]
  · intro u hu
    rw [hrun u]
    simpa [Cfg.Halted, leftCfg] using hlive u hu
```

**Duplication ledger: new copies: none.** The old action proof and induction are removed; the replacement cites the existing public proofs. Other inherited families remain untouched as required by the brief.

## Size and freeze

| Version | Lines | Public declarations | Private declarations |
|---|---:|---:|---:|
| Base | 5713 | 8 | 214 |
| After Task 1 | 5550 | 8 | 206 |
| Final | 5515 | 8 | 204 |

Task 1: `5713 - 163 = 5550` lines. Task 2: delete 52 lines of local forwarding lemmas and replace a 2-line consumer proof by 19 lines, giving `5550 - 52 - 2 + 19 = 5515`. Total reduction: **198 lines**.

`scope.log` records byte comparisons and SHA-256 hashes for all eight public declarations, including their complete signatures, statements, docstrings, and proof bodies. All are unchanged. Imports are byte-identical. The declaration inventory loses exactly the eight Task-1 targets and the two replaced proof lemmas; it gains nothing. The only retained declarations whose text differs are `loopHost_contracts` (the permitted sentence) and `emLoopHost_body_forward` (its proof body).

## Verification

Lean: `4.25.0`, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. No tracked toolchain, dependency, import, or checking-script changes were made. All tcslib compilation used `scripts/lean_check_tree.sh`; no `lake build` command was issued for tcslib.

The baseline completed all 65 listed modules, then the separately requested Catalog check. The supplied module-order list omits six prerequisites now imported by its facades: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`. These were compiled in dependency order without source changes. The interrupted bootstrap resumed at the unfinished module; earlier completed results were retained.

The baseline bootstrap has four inherited sorry warnings in untouched files, listed below. These are outside this batch. The owned file had zero admissions at the base and after both commits, and the final three requested module checks have zero sorry warnings.

```text
TCSlib/Complexity/TuringMachine/CounterProgRun.lean:343:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/NDCodes.lean:187:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Formulas/QBF.lean:119:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Formulas/QBFEncoding.lean:88:8: warning: declaration uses 'sorry'
```

Final ordered sweep summaries (complete diagnostics in `final-sweep.log`):

```text
RESULT TCSlib/Complexity/TuringMachine/Build/Loop: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
RESULT TCSlib/Complexity/TuringMachine/Build/Catalog: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
RESULT TCSlib/Complexity/TuringMachine: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
```

Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build` — **0 FAIL, 3 WARN**, the same pre-existing size-warning count as the base.

All eight final axiom prints are byte-identical to their baseline prints. `stateWord` uses no axioms; the seven theorems use exactly the three permitted standard axioms. There is no `sorryAx` in these footprints:

```text
'Turing.stateWord' does not depend on any axioms
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitLoopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_installCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final sweep and all pre-commit checks require a fresh nonempty `.olean`; the repository checker removes the prior artifact before invoking Lean. `git diff --check` passed, the working tree is clean, the two patches replayed sequentially from the recorded base and reproduced `Loop.lean` byte-for-byte, and `git bundle verify` passed. The bundle records the base above as its prerequisite and exposes `refs/heads/fill/retrofit-rb1` at the final commit.

## Delivery

The archive is flat, with no enclosing directory. It includes this report, the full `Loop.lean`, two numbered format-patches, `retrofit-rb1.bundle`, the final sweep and axiom-print logs, baseline axiom prints, per-task/commit/freeze/lint evidence, bootstrap evidence, delivery validation logs, and `SHA256SUMS`. `axioms.lean` supplies the eight print commands. SHA-256 checksums cover every payload file except the checksum manifest itself.
