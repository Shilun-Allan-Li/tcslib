"""Apply the review's minimal repairs to a copy of the delivered file, asserting each edit.

usage: python3 -I repairs.py <in.lean> <out.lean> <log> [ids...]
Each repair replaces an exact old text (which must occur exactly once) with a new text.
"""
import sys

REPAIRS = [
    ("R1", "ic_window_call: name the inner pair so the length rewrite avoids the input-position type",
     "  · rw [length_pairEncode] at hin\n    omega\n",
     "  · rw [length_pairEncode (Nat.bits t) α] at hin\n    omega\n"),
    ("R2", "ic_loop_replay: rewrite the replayed state with `rw` (simp does not see through the local let `c₀`)",
     "  · simpa only [semantic.1] using run\n",
     "  · rw [semantic.1] at run\n    exact run\n"),
    ("R3a", "ic_loopHost_run: `prefix` is a keyword; rename the hypothesis",
     "  obtain ⟨prefix, dispatch⟩ := phaseHostTM_run ic_loopPiece\n",
     "  obtain ⟨hpre, dispatch⟩ := phaseHostTM_run ic_loopPiece\n"),
    ("R3b", "ic_loopHost_run: the same rename at its use",
     "      rw [prefix u before, Cfg.mapState_state]\n",
     "      rw [hpre u before, Cfg.mapState_state]\n"),
    ("R4", "ic_replay_tail: aim the layout equation at the loop's end configuration, not the start",
     "  rw [vhostCfg_state, counter_cfg_eq, Option.map_some] at state\n",
     "  rw [vhostCfg_state, counter_cfg_eq _ e, Option.map_some] at state\n"),
    ("R5", "ic_time_ledger: give gcongr the summand template (it otherwise splits the constant)",
     "        gcongr <;> omega\n",
     "        gcongr ?_ + ?_ * _ + ?_ * _ + ?_ * _ <;> omega\n"),
    ("R6", "ic_loopHost_run (seam): the field equations of `Cfg.mapState` are stated pointwise; apply funext first",
     "    apply Cfg.ext <;> simp only [leaf, Cfg.mapState_state, Cfg.mapState_inputPos,\n"
     "      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,\n"
     "      Option.map_map, Function.comp_def]\n",
     "    apply Cfg.ext <;> (try funext i) <;> (try funext p) <;>\n"
     "      simp only [leaf, Cfg.mapState_state, Cfg.mapState_inputPos,\n"
     "        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,\n"
     "        Option.map_map, Function.comp_def]\n"),
    ("R7", "ic_loopHost_run (first verdict): rewrite the seam inside the verdict run, then close by defeq of the phase index (rw cannot match `ic_loopPh false` with the loop's state type)",
     "    rw [show T + 2 = (T + 1) + 1 by omega, MultiTapeTM.runFrom_add,\n      dispatch, seam, leafRun, Cfg.mapState_state, verdict, Option.map_some]\n",
     "    rw [show T + 2 = (T + 1) + 1 by omega, MultiTapeTM.runFrom_add, dispatch]\n"
     "    have final : ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom\n"
     "        (leaf.mapState (Sigma.mk true)) 1).state =\n"
     "        some ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ := by\n"
     "      rw [leafRun, Cfg.mapState_state, verdict, Option.map_some]\n"
     "    rw [← seam] at final\n"
     "    exact final\n"),
    ("R8", "ic_replay_rep (rule 10): the published field equations of `NDTM.withChoiceTape` and `Cfg.init` are pointwise; the verbatim `simpa` closed only by unfolding those two definitions (seal failure)",
     "  · intro i\n    simpa only [NDTM.withChoiceTape_workTapes, NDTM.withChoiceTape_workTapePos,\n      NDTM.initCfg_eq, Cfg.init_workTapes, Cfg.init_workTapePos] using hbank i\n",
     "  · intro i\n"
     "    have tapes : (N.initCfg x).workTapes = fun _ _ => none := by\n"
     "      funext j a\n"
     "      rw [NDTM.initCfg_eq, Cfg.init_workTapes]\n"
     "    have heads : (N.initCfg x).workTapePos = fun _ => 0 := by\n"
     "      funext j\n"
     "      rw [NDTM.initCfg_eq, Cfg.init_workTapePos]\n"
     "    obtain ⟨htape, hhead⟩ := hbank i\n"
     "    refine ⟨?_, ?_⟩\n"
     "    · funext a\n"
     "      rw [htape, NDTM.withChoiceTape_workTapes, tapes]\n"
     "    · rw [hhead, NDTM.withChoiceTape_workTapePos, heads]\n"),
]

def main():
    src, dst, log = sys.argv[1], sys.argv[2], sys.argv[3]
    ids = sys.argv[4:]
    text = open(src, encoding="utf-8").read()
    allr = REPAIRS
    out = []
    for rid, why, old, new in allr:
        if ids and rid not in ids:
            continue
        n = text.count(old)
        assert n == 1, f"{rid}: expected 1 occurrence, found {n}"
        text = text.replace(old, new)
        assert text.count(new) >= 1, f"{rid}: replacement not present"
        out.append(f"{rid}: applied ({why})")
    open(dst, "w", encoding="utf-8").write(text)
    open(log, "w", encoding="utf-8").write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == "__main__":
    main()
