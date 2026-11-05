> **Run (2026-11-05, the cloud maintainer session).** These probes were drafted by a sub-agent
> as text and then elaborated here, against `oleans-chk196`: a copy of the first cloud snapshot
> `oleans-cloud0` with #196's chain (`../chain/`) and the eight further modules of
> `extra-modules.txt` compiled into it (the README below names the Mac's `oleans-ldwa`, which does
> not exist on the cloud machine). Results (`runs.txt`, `*.out`): `BlockFitDeepen` **0 diagnostics**,
> so both steps marked `UNSURE` in its comments elaborate; `SealControl_NoEdge` 3 pass unsealed,
> 3 fail sealed; `SealControl_Fit` 54 pass and 1 fail unsealed (`Reach`'s recursive delta goal),
> 55 fail sealed. The head was `b1b5199b`, whose only change from `f2616fee` is a proof body in
> `CfgRecord` (the harvested step's `simp only`).

# Gate 96 (#196, repaired head `f2616fee`): the block fit joined to the window lemmas (finding 1)

Prepared as text, not elaborated. Repaired head: `f2616fee1d41f75600bc9070db149d32a0c69acc`.
`NoEdge` and `noEdge_iff` are in `SavitchARM/Window.lean` (`noEdge_iff := Iff.rfl`, l. 74). The APIs
the old probe uses (`rel_iff_orc`, `initO_iff_orc`, `accO_iff_orc`, `stepRel_iff_mem`, `outerU_run`,
`AHalt.embed_guardLe`, `A_noVal`, `setSt_toV`, `outerSt_toV`, `indicator_eq_decide`) are unchanged at
`f2616fee`.

## Files

| File | Purpose | Import line(s) | Expected |
|---|---|---|---|
| `BlockFitDeepen.lean.txt` | The gate's `BlockFitReal`, extended (see below) | `import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct`, `import TCSlib.Complexity.SpaceComplexity.SavitchARM.Window` | **0 diagnostics** (by inspection; two steps are marked `UNSURE`) |
| `SealControl_NoEdge_unsealed.lean.txt` / `_sealed.lean.txt` | `NoEdge`'s controls: `#ctl_rfl` (the delta goal `NoEdge = fun N x s w => ¬ ∃ …`), `#ctl_eqn` (`NoEdge.eq_1` by `intros; rfl`) and `#ctl_stmt Complexity.LogProg.SavitchARM.noEdge_iff` (`noEdge_iff`'s statement by `Iff.rfl`, the equation goal) | `import TCSlib.Complexity.SpaceComplexity.SavitchARM.Window` | unsealed **3 × `CONTROL_PASS`**; sealed **3 × `CONTROL_FAIL`** |
| `SealControl_Fit_unsealed.lean.txt` / `_sealed.lean.txt` | An extra: two goals for every definition `BlockFitDeepen` seals, plus `noEdge_iff`. That is 27 definitions, 55 controls: the Fit section's 22, `NoEdge`, and the `Loop` section's `FinNDTM.DecidesInSpace`, `Codec.codeK`, `logSpace`, `pairEncode`. The old probe's 22 had no recorded controls of their own; the evidence covers some of them, in `rule10/` and `route/window-seal/`. | `Correct` and `Window`, as above | unsealed **54 × `CONTROL_PASS`, 1 × `CONTROL_FAIL`**: `rfl Complexity.LogProg.SavitchARM.Reach`, which is recursive, as in the gate's rule10 controls. Sealed, **55 × `CONTROL_FAIL`**. |
| `mkblockfit.py` | `python3 -I mkblockfit.py <evidence/route/BlockFitReal.lean.txt> deepen-steps.lean.part.txt <out>` writes `BlockFitDeepen.lean.txt`. It makes four edits, each at an anchor asserted to occur once. | | |
| `deepen-steps.lean.part.txt` | The new `section Loop`, on its own | | |
| `mkctl_noedge.py` | `python3 -I mkctl_noedge.py <evidence/rule10/ctl_header.lean.part.txt> <out dir>` writes the four control files. The gate's header is used verbatim, plus a `#ctl_stmt` command. | | |
| `recompile-order.txt` | The 24 modules to compile, in order, before these files elaborate | | |

**Oleans.** Every file needs #196's repaired tree. Between `89f4ebbc` and `f2616fee` seven Lean files
changed: `Radius`, `PathWalk`, `Reach`, `Recursion`, `Search`, `Window` and `CfgRecord`. Within the
116-module closure of `Correct` and `Window`, 24 modules sit downstream of those files
(`recompile-order.txt`, from `CfgRecord` to `Window`). Either:
- compile those 24, in order, with `leanelab-o.sh`, into a copy-on-write clone of `oleans-ldwa`, and
  elaborate against that overlay; or
- use the snapshot of the merged-tree replay re-run at `f2616fee`.

`oleans-ldwa` alone is stale. Its `Reach` still imports `ISCountMath`, and its `Window` has no
`noEdge_iff`.

## What the probe adds (`BlockFitDeepen` against `BlockFitReal`)

1. It imports `SavitchARM.Window`. This introduces no new name ambiguity: `Reach` and `rU` were
   already overloaded (`Complexity.Codec.Reach` and `Complexity.Codec.rU` are abbrevs with other
   types), and they resolve as before.
2. `Complexity.LogProg.SavitchARM.NoEdge` joins the Fit section's `[local irreducible]` list. That
   section also keeps its `[-simp]` erasure.
3. A new `section Loop` sits inside `section Fit`, under that seal. It adds
   `[local irreducible] Turing.FinNDTM.DecidesInSpace Complexity.Codec.codeK Complexity.logSpace
   Turing.pairEncode`, the definitions that the window lemmas' hypotheses name. It contains three
   theorems:
   - `fit_edge_bit_eq_false_iff` (**the join**): the exit bit `decide P_s` of `fit_edge_block` is
     `false` iff `NoEdge N x s w`. Proof: `rw [decide_eq_false_iff_not, noEdge_iff]`.
   - `deepen_step_exit_false` (**loop step (i)**): the block's hypotheses, together with
     `h : N.DecidesInSpace L sp` and `hw : codeK N * (s + logSpace |x| + 1) ≤ w`, give
     `∃ b v₂'` with `fit_edge_block`'s three conclusions at exit `k b` and
     `b = false → (x ∈ L ↔ ∃ u < 2^w, … ∈ initLang N ∧ ∃ v < 2^w, … ∈ acceptLang N ∧ Reach (2^w) (StepRel N x s) w u v)`.
     Proof: `fit_edge_block`, then `mem_iff_reach_of_noEdge`, with `NoEdge` obtained by
     `rw [noEdge_iff]` and `decide_eq_false_iff_not.mp`.
   - `deepen_step_exit_of_lt` (**loop step (ii)**): the same hypotheses, with
     `hs : sp |x| < s` instead of `hw`, give `fit_edge_block`'s conclusion with the exit fixed at
     `k false`. Proof: `rw [decide_eq_false_iff_not.mpr (noEdge_iff.mp (noEdge_of_lt h x s w hs))] at h3`.

   None of the three unfolds `NoEdge`. They use `noEdge_iff` in both directions, apply
   `noEdge_of_lt` and `mem_iff_reach_of_noEdge`, and do not reduce `decide`. The core lemma
   `decide_eq_false_iff_not` takes its `Decidable` instance as an implicit argument (`{_ : Decidable p}`,
   `Init/SimpLemmas.lean`), so `rw` and `.mp` pick up the classical instance of `fit_edge_block`'s
   statement by unification and never synthesize a second one.

## Unsure (marked `UNSURE` in the file)

- In step (i), the final `exact decide_eq_false_iff_not.mp hb` needs the predicate inside
  `fit_edge_block`'s `decide` and the right-hand side of `noEdge_iff` to elaborate to the same term.
  Their text is identical and both resolve to the `SavitchARM` names, but this was not elaborated.
  The same holds for the closing `rfl` of `fit_edge_bit_eq_false_iff`'s `rw`. If either fails,
  `simpa only [decide_eq_false_iff_not] using hb` shows the difference.
- In step (ii), `rw [decide_eq_false_iff_not.mpr …] at h3` leaves the instance as a metavariable for
  `rw` to assign by matching. This is standard, but not run.
- The `Fit` controls' unsealed result assumes that the only recursive definition among the 27 is
  `Reach`. I read the other bodies (`A`, `Ins.embed`, `PreS` are pattern matches; `AReach` and
  `AHalt` are existentials over `arun`).
