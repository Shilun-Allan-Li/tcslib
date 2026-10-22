"""Apply the reviewer's minimal repairs to the verbatim draft-inserted InputWindow.lean.

Usage: python3 -I repairs.py IN.lean OUT.lean [LAST_REPAIR_ID]

Each repair is an exact (old, new) replacement asserted to occur exactly once. Repairs are
applied in order; LAST_REPAIR_ID stops after that repair (for bisecting).
"""
import sys

REPAIRS = [
    # R1: layout only. Lean's structure-instance field list must not start a continuation line
    # left of its first field's column; put the first field on its own line.
    ("R1", "iw_body_copy statement: structure-instance layout",
     """      { c with state := some false, inputPos := moveInputPos c.inputPos 1,
        workTapes := fun i => Function.update (c.workTapes i) (c.workTapePos i) (some b),
        workTapePos := fun i => c.workTapePos i + 1 } := by""",
     """      { c with
        state := some false, inputPos := moveInputPos c.inputPos 1,
        workTapes := fun i => Function.update (c.workTapes i) (c.workTapePos i) (some b),
        workTapePos := fun i => c.workTapePos i + 1 } := by"""),
    # R2: Mathlib renames at the pin (`update_same` -> `update_self`, `update_noteq` ->
    # `update_of_ne`, same statements).
    ("R2a", "Mathlib rename update_same",
     "    rw [Function.update_same]\n",
     "    rw [Function.update_self]\n"),
    ("R2b", "Mathlib rename update_noteq (outer)",
     "  · rw [Function.update_noteq he]\n",
     "  · rw [Function.update_of_ne he]\n"),
    ("R2c", "Mathlib rename update_noteq (inner)",
     "        Function.update_noteq (by omega)]\n",
     "        Function.update_of_ne (by omega)]\n"),
    # R3: `apply Cfg.ext rfl` lets `rfl` identify the two implicit configurations before the
    # goal is seen; `refine` elaborates against the goal first.
    ("R3", "iw_prefix_step: Cfg.ext with the goal as expected type",
     "  rw [iw_body_copy _ _ rfl hbit]\n  apply Cfg.ext rfl\n",
     "  rw [iw_body_copy _ _ rfl hbit]\n  refine Cfg.ext rfl ?_ ?_ ?_ ?_\n"),
    # R4: `counterLoopOrbit` is an abbrev; after `simp only [roundOrbit_succ]` the goal shows
    # `roundOrbit`, so `rw [ih _]` does not fire (the brief's pitfall). Close by `exact`.
    ("R4", "iw_orbit: close the successor case by exact (abbrev pitfall)",
     """    simp only [roundOrbit_succ]
    rw [ih (by omega)]
    exact iw_prefix_step c p r (by omega)
""",
     """    simp only [roundOrbit_succ]
    exact (congrArg (fun x => iw_body.runFrom x 1) (ih (by omega))).trans
      (iw_prefix_step c p r (by omega))
"""),
    # R5: layout only. A tactic block's continuation line must be right of its first tactic.
    ("R5", "iw_local statement: tactic-block layout",
     """          (iw_prefix c p n (by have := Nat.min_le_right
            (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p); omega)) (iw_patch ct cp v) cp ∧""",
     """          (iw_prefix c p n (by
            have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
            omega)) (iw_patch ct cp v) cp ∧"""),
    # R6: `simp` cannot rewrite the argument of `Function.update` (its value type is a
    # dependent lambda); rewrite the index and evaluate the update explicitly.
    ("R6", "iw_patch_append: evaluate the appended cell by rw",
     "    rw [if_pos (by omega), FinTM.bufferTape_append]\n    simp\n",
     "    rw [if_pos (by omega), FinTM.bufferTape_append, add_sub_cancel_left, Function.update_self]\n"),
    # R7: the copy step moves by `(1 : SignType)`, which `rw` does not match against
    # `SignType.pos` in `moveInputPos_pos_of_ne_right`; restate the literal first
    # (Mathlib's `SignType.pos_eq_one`).
    ("R7", "iw_prefix_step: (1 : SignType) is SignType.pos",
     "    rw [moveInputPos_pos_of_ne_right _ (by simp only [iw_prefix]; omega)]\n",
     "    rw [← SignType.pos_eq_one,\n"
     "      moveInputPos_pos_of_ne_right _ (by simp only [iw_prefix]; omega)]\n"),
    # R8: the round time `(fun _ => 1) _` is not beta-reduced in the loop lemmas' hypotheses:
    # `decide` rejects the free variables and `omega` sees an atom. Use `Nat.one_pos`, and
    # beta-reduce before `omega`.
    ("R8a", "iw_local exhaustion: round hypotheses with a beta-redex round time",
     "        refine ⟨?_, by decide, (fun u hu hu' => by omega), ?_⟩\n",
     "        refine ⟨?_, Nat.one_pos, (fun u hu hu' => by dsimp only at hu'; omega), ?_⟩\n"),
    ("R8b", "iw_local escape: round hypotheses with a beta-redex round time",
     "        refine ⟨?_, by decide, (fun u hu hu' => by omega)⟩\n",
     "        refine ⟨?_, Nat.one_pos, (fun u hu hu' => by dsimp only at hu'; omega)⟩\n"),
    # R9: `subst n` eliminated `n` through `hn` (`n = min ..`), not `hnd` (`n = d`).
    ("R9", "iw_local exhaustion: substitute through hnd",
     "  · have hnd : n = d := hn.trans (Nat.min_eq_left hd)\n    subst n\n",
     "  · have hnd : n = d := hn.trans (Nat.min_eq_left hd)\n    subst hnd\n"),
    # R10: the abbrev pitfall again (as R4), in the final escape round.
    ("R10", "iw_local escape: final round by exact (abbrev pitfall)",
     """      simp only [roundOrbit_succ]
      rw [horbit n (by omega)]
      exact iw_body_blank _ rfl (Cfg.inputSymbol_of_end (by simp only [iw_prefix]; omega))
""",
     """      simp only [roundOrbit_succ]
      exact (congrArg (fun x => iw_body.runFrom x 1) (horbit n (by omega))).trans
        (iw_body_blank _ rfl (Cfg.inputSymbol_of_end (by simp only [iw_prefix]; omega)))
"""),
    # R11: `iw_patch` unfolds only when applied to a cell, and its interval uses `v.length`;
    # close the escape endpoint through funext and `counterWord_length`.
    ("R11", "iw_local escape: endpoint tape through funext and counterWord_length",
     "      simp only [counter_cfg_eq, iw_patch]\n",
     "      have hpatch : iw_patch ct cp (counterWord w (n + 1)) = fun q =>\n"
     "          if cp ≤ q ∧ q < cp + (w.length : ℤ) then\n"
     "            FinTM.bufferTape (counterWord w (n + 1)) (q - cp)\n"
     "          else ct q := by\n"
     "        funext q\n"
     "        simp only [iw_patch, counterWord_length]\n"
     "      simp only [counter_cfg_eq, hpatch]\n"),
    # R12: `simp` does not evaluate `Fin.lastCases` at the numerals `0, 1 : Fin 2` that
    # `fin_cases` produces; both remaining facts hold by `rfl`.
    ("R12a", "target hstart: Fin.lastCases at numerals by rfl",
     "      fin_cases i <;> simp [start, counter_cfg_eq, body, ι, iw_select]\n",
     "      fin_cases i <;> simp [start, counter_cfg_eq, body, ι, iw_select] <;> exact ⟨rfl, rfl⟩\n"),
    ("R12b", "target hend: Fin.lastCases at numerals by rfl",
     """        simp [finish, counter_cfg_eq, out, iw_prefix, body, ι, iw_select, htake, hjd,
          Ne.symm hjd]
""",
     """        simp [finish, counter_cfg_eq, out, iw_prefix, body, ι, iw_select, htake, hjd,
          Ne.symm hjd] <;> exact ⟨rfl, rfl⟩
"""),
    # R13: the statement's `y` is the local `let`; unfold it, and match the counter interval's
    # width `v.length = w.length` before closing by unfolding the file's own `iw_patch`.
    ("R13a", "target inputPos clause: unfold the local y",
     "  · simp only [he, out, iw_prefix]\n",
     "  · simp only [he, out, iw_prefix, y]\n"),
    ("R13b", "target workTapes clause: width and own-definition unfolding",
     "  · rw [he]\n    simp only [out, iw_patch, hv]\n",
     "  · rw [he, ← hv]\n    rfl\n"),
    ("R13c", "target workTapePos clause: unfold the local y",
     "  · simp only [he, out]\n  · simp only [he, out]\n  · intro u hu\n",
     "  · simp only [he, out, y]\n  · simp only [he, out]\n  · intro u hu\n"),
    # R14: lint only. `iw_local`'s hypothesis `p ≤ |z|` is unused (the prefix bound comes
    # from `hn`); mark it unused so the module has no warning.
    ("R14", "iw_local: unused hypothesis marked",
     "    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (hp : p ≤ z.length)\n"
     "    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)\n",
     "    (hc : c.state = some false) (hi : c.inputPos.val = p + 1) (_hp : p ≤ z.length)\n"
     "    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)\n"),
]


def main():
    src, dst = sys.argv[1], sys.argv[2]
    last = sys.argv[3] if len(sys.argv) > 3 else None
    text = open(src, encoding="utf-8").read()
    for rid, why, old, new in REPAIRS:
        n = text.count(old)
        assert n == 1, f"{rid}: expected exactly one occurrence, found {n}"
        text = text.replace(old, new)
        print(f"applied {rid}: {why}")
        if rid == last:
            break
    open(dst, "w", encoding="utf-8").write(text)


main()
