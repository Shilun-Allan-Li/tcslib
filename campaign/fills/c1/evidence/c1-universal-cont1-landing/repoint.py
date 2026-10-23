import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
def rep(old, new, n=1):
    global s
    c = s.count(old); assert c == n, (old[:70], c, n); s = s.replace(old, new)
def cut(start, stop):
    global s
    assert s.count(start) == 1 and s.count(stop) == 1, (start[:50], stop[:50])
    i = s.index(start); j = s.index(stop); assert i < j
    s = s[:i] + s[j:]
rep("import TCSlib.Complexity.TuringMachine.Build.Rewind\n",
    "import TCSlib.Complexity.TuringMachine.Build.Rewind\nimport TCSlib.Complexity.TuringMachine.Build.InputRewind\n")
# the private leaf, its run, and the collapse lemma
cut("/-- **The input rewind leaf** (`Turing.FinTM.controlAction`)",
    "/-- Collapsing a constant state relabeling over any previous relabeling. -/")
cut("/-- Collapsing a constant state relabeling over any previous relabeling. -/",
    "/-- One seam step whose previous endpoint arrives as a right-tagged configuration")
rep("  have hcomp := un_mapState_comp c₂ g entry\n",
    "  have hcomp : (c₂.mapState g).mapState (fun _ => entry) = c₂.mapState fun _ => entry := by\n"
    "    rw [Cfg.mapState_mapState]; rfl\n")
# the machine, its seam, the exit and the endpoint
rep("  let A8 : MultiTapeTM (K + MC.k + 1) Bool (Fin 3) := un_inRewTM (K + MC.k + 1)\n",
    "  let A8 : MultiTapeTM (K + MC.k + 1) Bool InputRewindPhase := inputRewindTM (K + MC.k + 1)\n")
rep("  let R8 := seamCompTM R7 (Sum.inr SweepPhase.done) A8 (0 : Fin 3)\n",
    "  let R8 := seamCompTM R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start\n")
rep("    Sum.inr (2 : Fin 3), fun α => ?_⟩\n", "    Sum.inr InputRewindPhase.done, fun α => ?_⟩\n")
rep("  let E8 : Cfg (K + MC.k + 1) Bool (Fin 3) z := ⟨some 2, 1, tp7, fun _ => 0, []⟩\n",
    "  let E8 : Cfg (K + MC.k + 1) Bool InputRewindPhase z := ⟨some .done, 1, tp7, fun _ => 0, []⟩\n")
# phase 8
old8 = """  have hs8 : A8.runFrom (E7.mapState fun _ => (0 : Fin 3)) T8 = E8 ∧
      E8.state = some 2 ∧
      ∀ v < T8, (A8.runFrom (E7.mapState fun _ => (0 : Fin 3)) v).state ≠ some 2 := by
    have hip8 : (E7.mapState fun _ => (0 : Fin 3)).inputPos = ip23 :=
      Cfg.mapState_inputPos _ _
    obtain ⟨hrun8, hcut8⟩ := un_inRew_run (E7.mapState fun _ => (0 : Fin 3))
      (by rw [Cfg.mapState_state]; rfl)
      (by rw [hip8]; show 1 ≤ 2 * u.length + 3; omega)
    have hT8 : (E7.mapState fun _ => (0 : Fin 3)).inputPos.val + 1 = T8 := by
      rw [hip8]
    rw [hT8] at hrun8 hcut8
    refine ⟨hrun8.trans ?_, rfl, hcut8⟩
    refine Cfg.ext rfl rfl ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => (0 : Fin 3)) E7 i)
      (Cfg.mapState_output (fun _ => (0 : Fin 3)) E7)
    funext i q
    exact Cfg.mapState_workTapes (fun _ => (0 : Fin 3)) E7 i q
"""
new8 = """  have hs8 : A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) T8 = E8 ∧
      E8.state = some .done ∧
      ∀ v < T8, (A8.runFrom (E7.mapState fun _ => InputRewindPhase.start) v).state ≠
        some .done := by
    have hip8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos = ip23 :=
      Cfg.mapState_inputPos _ _
    obtain ⟨hrun8, hcut8, -⟩ := inputRewindTM_run (E7.mapState fun _ => InputRewindPhase.start)
      (by rw [Cfg.mapState_state]; rfl)
      (by rw [hip8]; show 1 ≤ 2 * u.length + 3; omega)
    have hT8 : (E7.mapState fun _ => InputRewindPhase.start).inputPos.val + 1 = T8 := by
      rw [hip8]
    rw [hT8] at hrun8 hcut8
    refine ⟨hrun8.trans ?_, rfl, hcut8⟩
    refine Cfg.ext rfl rfl ?_
      (funext fun i => Cfg.mapState_workTapePos (fun _ => InputRewindPhase.start) E7 i)
      (Cfg.mapState_output (fun _ => InputRewindPhase.start) E7)
    funext i q
    exact Cfg.mapState_workTapes (fun _ => InputRewindPhase.start) E7 i q
"""
rep(old8, new8)
rep("  have hch8 := un_step' R7 (Sum.inr SweepPhase.done) A8 (0 : Fin 3) (2 : Fin 3)\n",
    "  have hch8 := un_step' R7 (Sum.inr SweepPhase.done) A8 InputRewindPhase.start\n"
    "    InputRewindPhase.done")
# hch8's next line starts with four spaces and Sum.inr; join it onto the new second line
rep("    InputRewindPhase.done    Sum.inr hch7.1 hch7.2.1 hch7.2.2 hs8.1 rfl hs8.2.2\n",
    "    InputRewindPhase.done Sum.inr hch7.1 hch7.2.1 hch7.2.2 hs8.1 rfl hs8.2.2\n")
# the endpoint and the composite's state type
rep("(Sum.inr : Fin 3 → _)", "(Sum.inr : InputRewindPhase → _)", 6)
rep("some (Sum.inr (2 : Fin 3))", "some (Sum.inr InputRewindPhase.done)")
rep("⊕ SweepPhase) ⊕ Fin 3) z)", "⊕ SweepPhase) ⊕ InputRewindPhase) z)", 3)
for gone in ("un_inRewTM", "un_inRew_run", "un_mapState_comp"):
    assert gone not in s, gone
open(p, 'w', encoding='utf-8').write(s)
print("ok")
