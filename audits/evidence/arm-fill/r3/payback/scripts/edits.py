"""The edits of the dedup payback landing, one function per touched file (read-only on the base).

Every edit is asserted: `lib.sub` requires the stated occurrence count, `lib.delete_decl` and
`lib.make_public` a unique declaration, `lib.d1_rewrite` the stated counts of code and comment
occurrences of `InWin`. Each function takes the base text and returns the landed text; `log`
records one line per edit (land.py writes them to logs/land-edits.txt).

The metadata at the end (FILES, KIND, D1, PROMOTED, ADDED, DELETED, MOVED, DELTAS) drives the
cuts, the freeze, the name screen and the ledger map.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
from lib import sub  # noqa: E402

TMP = os.path.join(lib.L, "work", "tmp-scan")
SC = lib.SC
C = lib.C


def dels(t, names, log, what):
    for n in names:
        t = lib.delete_decl(t, n, TMP)
        log(f"  delete {n}")
    return t


def pub(t, names, log):
    for n in names:
        t = lib.make_public(t, n, TMP)
        log(f"  make public {n}")
    return t


# ============================================================================ ConfigGraph

CG_BOUNDS = '''/-- **A windowed configuration meets the bounds of the core code**: every work head and
every nonblank work cell of a configuration in the radius-`s` window (`Turing.Cfg.InWindow`)
lies in `[-s, s]` — the hypothesis form of
`Turing.MultiTapeTM.ConfigCount.coreCode_inj`. [AB09, Claim 4.4(1)]

**Proof sketch.** The head bounds are the window's; a nonblank cell outside `[-s, s]` would
contradict the window's blank-outside clause. -/
theorem Cfg.InWindow.core_bounds {s : ℕ} {c : Cfg k Bool S x} (hc : c.InWindow s) :
    ∀ i, |c.workTapePos i| ≤ s ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ s := by
  intro i
  refine ⟨hc.1 i, ?_⟩
  intro z hz
  by_contra hn
  exact hz (hc.2 i z (lt_of_not_ge hn))
'''

CG_EMPTY = '''/-- An output summary is empty exactly for the empty output. [AB09, §4.1.1]

**Proof sketch.** Inspect the empty, singleton, and longer output words. -/
theorem outSummary_eq_empty_iff (u : List Bool) : outSummary u = .empty ↔ u = [] := by
  cases u with
  | nil => simp [outSummary]
  | cons a u => cases u <;> cases a <;> simp [outSummary]
'''

CG_MEM = '''/-- **An accepting branch of any length gives membership**: if `N` decides `L` (in any
space bound), an accepting branch of `N` on `x` of any length `t` makes `x` a member of `L`.
[AB09, §4.1.1]

**Proof sketch.** Compare `t` with the halting budget `T` of `x`. If `t ≤ T`, pad the branch
to length `T` (`Turing.FinNDTM.AcceptsWithin.mono`). Otherwise its `T`-prefix has halted
(`Turing.NDTM.HaltsWithin`), so the run is frozen from there (`Turing.NDTM.runWith_of_halt`)
and the prefix accepts. Either way the equivalence at `T` gives membership. -/
theorem DecidesInSpace.mem_of_acceptsWithin {N : FinNDTM Bool} {L : Language Bool}
    {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp) {t : ℕ} (ha : N.AcceptsWithin x t) : x ∈ L := by
  obtain ⟨T, halt, -, iff_at_T⟩ := h x
  apply iff_at_T.mpr
  by_cases ht : t ≤ T
  · exact ha.mono ht
  · obtain ⟨w, hw, _, output⟩ := ha
    have prefix_length : (w.take T).length = T := List.length_take_of_le (by omega)
    have prefix_halt := halt (w.take T) prefix_length
    have frozen : N.tm.runWith w (N.tm.initCfg x) = N.tm.runWith (w.take T) (N.tm.initCfg x) := by
      conv_lhs => rw [← List.take_append_drop T w]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ prefix_halt]
    exact ⟨w.take T, prefix_length, prefix_halt, by rw [← frozen]; exact output⟩
'''

CG_S1B = ["s1b_record", "s1b_record_eq_iff", "s1b_recordEdge", "s1b_recordPath_lift",
          "s1b_recordPath_of_run", "s1b_record_accepts", "s1b_count_le_exp",
          "s1b_constructor_count", "s1b_vertex_count", "s1b_normalize_radius",
          "s1b_constructor_time"]
CG_PROMOTE = ["take_succ_action", "abs_lt_card_visitedWith", "mem_visitedWith_of_ne_none",
              "visitedWith_take_subset", "runWith_take_inWindow", "inWindow_of_coreSum_eq"]


def e_ConfigGraph(t, log):
    # module docstring: the s1b sentence goes with the block; new main results; the window
    t = sub(t, "`TCSlib.Complexity.SpaceComplexity.ExpTime` (2026-10-14). The private `s1b_*` "
            "helpers below\nbelong to the superseded record-table route of the S1b partial fill "
            "and have no consumer.\n", "`TCSlib.Complexity.SpaceComplexity.ExpTime` "
            "(2026-10-14).\n", 1, "CG doc s1b")
    t = sub(t, "* **The graph is the step relation, not a finite object**",
            "* **The coding window is `Turing.Cfg.InWindow`** (`Build/CfgRecord.lean`): every work\n"
            "  head in `[-s, s]` and every work cell outside it blank, the predicate the record\n"
            "  carrier and the configuration codec share.\n"
            "* **The graph is the step relation, not a finite object**", 1, "CG doc window")
    t = sub(t, "* `Turing.outSummary_eq_accept_iff` — the summary recognizes exactly `[true]`.\n",
            "* `Turing.outSummary_eq_accept_iff`, `Turing.outSummary_eq_empty_iff` — the summary\n"
            "  recognizes exactly `[true]`, and the empty output.\n", 1, "CG doc summary")
    t = sub(t, "* `Turing.FinNDTM.not_acceptsWithin_zero` — acceptance requires a transition.\n",
            "* `Turing.FinNDTM.not_acceptsWithin_zero` — acceptance requires a transition.\n"
            "* `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin` — an accepting branch of any\n"
            "  length gives membership.\n"
            "* `Turing.NDTM.runWith_take_inWindow` — every prefix of a space-bounded branch lies\n"
            "  in the coding window, from the visited-set facts `Turing.NDTM.take_succ_action`,\n"
            "  `Turing.NDTM.abs_lt_card_visitedWith`, `Turing.NDTM.mem_visitedWith_of_ne_none`,\n"
            "  `Turing.NDTM.visitedWith_take_subset`.\n"
            "* `Turing.NDTM.inWindow_of_coreSum_eq` — the window depends only on the vertex.\n"
            "* `Turing.Cfg.InWindow.core_bounds` — the window gives the bounds of `coreCode_inj`.\n",
            1, "CG doc results")
    log("  module docstring: s1b sentence removed; the window bullet; five Main results bullets")
    # G-outsum: the empty-output sibling, beside outSummary_eq_accept_iff
    d0, s0, e0, ls = lib.locate(t, "outSummary_eq_accept_iff", TMP)
    t = "\n".join(ls[:e0 + 1] + [""] + CG_EMPTY.rstrip("\n").split("\n") + ls[e0 + 1:])
    log(f"  insert outSummary_eq_empty_iff after outSummary_eq_accept_iff (base line {s0 + 1})")
    # D1: the private window and its bridge go; the core-code bounds lemma comes in
    t = dels(t, ["inWindow_iff_cfgInWindow", "InWindow"], log, "CG")
    t = sub(t, "namespace NDTM\n\n/-- The configuration-graph **vertex**",
            CG_BOUNDS + "\nnamespace NDTM\n\n/-- The configuration-graph **vertex**", 1, "CG bounds")
    log("  insert Cfg.InWindow.core_bounds before `namespace NDTM`")
    code = lib.blank_comments(t)
    n = len([1 for i in range(len(code)) if code.startswith("InWindow s ", i)
             and (i == 0 or not (code[i - 1].isalnum() or code[i - 1] in "._"))])
    assert n == 5, n
    t = lib.d1_private(t, 5)
    log("  D1: the 5 code uses `InWindow s _` -> `Cfg.InWindow s _`")
    # D2, D2h, D5: promote the originals
    t = pub(t, CG_PROMOTE, log)
    # runWith_take_inWindow: the conjunction is now (heads) ∧ (blank outside)
    t = sub(t, '''    InWindow s (tm.runWith (w.take j) (tm.initCfg x)) := by
  intro i
  have card_bound : (tm.visitedWith w (tm.initCfg x) i).card ≤ s :=
    (Finset.single_le_sum (f := fun i => (tm.visitedWith w (tm.initCfg x) i).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs
  have bounded (z : ℤ) (hz : z ∈ tm.visitedWith (w.take j) (tm.initCfg x) i) : |z| ≤ s := by
    have hz' := visitedWith_take_subset tm w (tm.initCfg x) j i hz
    have small := abs_lt_card_visitedWith tm w i hz'
    omega
  constructor
  · apply bounded
    apply Finset.mem_image.mpr
    exact ⟨(w.take j).length, Finset.mem_range.mpr (Nat.lt_succ_self _), by
      rw [List.take_length]⟩
  · intro z hz
    exact bounded z (mem_visitedWith_of_ne_none tm (w.take j) i z hz)
'''.replace("    InWindow s", "    Cfg.InWindow s"), '''    Cfg.InWindow s (tm.runWith (w.take j) (tm.initCfg x)) := by
  have bounded (i : Fin k) (z : ℤ) (hz : z ∈ tm.visitedWith (w.take j) (tm.initCfg x) i) :
      |z| ≤ s := by
    have card_bound : (tm.visitedWith w (tm.initCfg x) i).card ≤ s :=
      (Finset.single_le_sum (f := fun i => (tm.visitedWith w (tm.initCfg x) i).card)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs
    have hz' := visitedWith_take_subset tm w (tm.initCfg x) j i hz
    have small := abs_lt_card_visitedWith tm w i hz'
    omega
  refine ⟨fun i => bounded i _ ?_, fun i z outside => ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(w.take j).length, Finset.mem_range.mpr (Nat.lt_succ_self _), by
      rw [List.take_length]⟩
  · by_contra nonblank
    exact (not_le_of_gt outside)
      (bounded i z (mem_visitedWith_of_ne_none tm (w.take j) i z nonblank))
''', 1, "CG runWith_take_inWindow proof")
    t = sub(t, "  simpa only [InWindow, tapes, heads] using hd\n",
            "  simpa only [Cfg.InWindow, tapes, heads] using hd\n", 1, "CG inWindow_of_coreSum_eq")
    t = sub(t, "/-- Window validity depends only on the configuration-graph vertex. -/\n",
            "/-- **Window validity depends only on the configuration-graph vertex**: a configuration\n"
            "with the vertex of a configuration in the radius-`s` window is in that window too.\n"
            "[AB09, §4.1.1]\n\n**Proof sketch.** Equal vertices have equal work tapes and heads, "
            "which is all the\nwindow reads. -/\n", 1, "CG inWindow_of_coreSum_eq doc")
    log("  runWith_take_inWindow, inWindow_of_coreSum_eq: proofs for the public window")
    t = sub(t, '''        (window a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)))
        (window b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)))
''', '''        (window a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))).core_bounds
        (window b (Nat.le_of_lt_succ (Finset.mem_range.mp hb))).core_bounds
''', 1, "CG count_windowed_vertices")
    log("  count_windowed_vertices: coreCode_inj through Cfg.InWindow.core_bounds")
    # D3: the any-length membership lemma, and the packaged interface's backward branch
    t = sub(t, "/-- **The packaged graph interface** (proved — phase P4.2): a\n",
            CG_MEM + "\n/-- **The packaged graph interface** (proved — phase P4.2): a\n", 1, "CG mem")
    t = sub(t, '''the vertex count. Backward: given an accepting branch at the vertex-count
budget, compare with `T`: if the budget exceeds `T`, the branch's `T`-prefix
is already halted (`Turing.NDTM.HaltsWithin`) with the run frozen
(`Turing.NDTM.runWith_of_halt`), so the prefix accepts and membership follows
from the equivalence at `T`; otherwise pad
(`Turing.FinNDTM.AcceptsWithin.mono`). -/''', '''the vertex count. Backward: an accepting branch at the vertex-count budget is an
accepting branch, which gives membership
(`Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`). -/''', 1, "CG mem_iff sketch")
    t = sub(t, '''  obtain ⟨T, halt, space, iff_at_T⟩ := h x
  constructor
  · intro member
    exact acceptsWithin_of_spaceUsedWith_le N (iff_at_T.mp member) space
  · intro accepts
    apply iff_at_T.mpr
    by_cases budget : N.configBound x.length (s x.length) ≤ T
    · exact accepts.mono budget
    · obtain ⟨w, hw, _, output⟩ := accepts
      have prefix_length : (w.take T).length = T := List.length_take_of_le (by omega)
      have prefix_halt := halt (w.take T) prefix_length
      have frozen : N.tm.runWith w (N.tm.initCfg x) =
          N.tm.runWith (w.take T) (N.tm.initCfg x) := by
        conv_lhs => rw [← List.take_append_drop T w]
        rw [NDTM.runWith_append, NDTM.runWith_of_halt _ prefix_halt]
      exact ⟨w.take T, prefix_length, prefix_halt, by rw [← frozen]; exact output⟩
''', '''  obtain ⟨T, -, space, iff_at_T⟩ := h x
  constructor
  · intro member
    exact acceptsWithin_of_spaceUsedWith_le N (iff_at_T.mp member) space
  · exact h.mem_of_acceptsWithin
''', 1, "CG mem_iff proof")
    log("  insert DecidesInSpace.mem_of_acceptsWithin; mem_iff_acceptsWithin_configBound's "
        "backward branch cites it")
    # the dead s1b block
    t = dels(t, CG_S1B, log, "CG s1b")
    t = sub(t, "end FinNDTM\n\nend Turing\n\nnamespace Complexity\n\nopen Turing\n\nend Complexity\n",
            "end FinNDTM\n\nend Turing\n", 1, "CG empty Complexity block")
    log("  the emptied `namespace Complexity` block removed")
    return t


# ============================================================================ D1: Codec/Word

def e_Word(t, log):
    t = sub(t, "* `Complexity.Codec.InWin` — heads and nonblank work cells lie in `[-s, s]`.\n",
            "", 1, "Word doc InWin bullet")
    t = sub(t, "This codec is configuration-graph infrastructure, not a result of [AB09]; its "
            "conventions\n(window `[-s, s]`, the output summary) are those of "
            "`TCSlib.Complexity.SpaceComplexity.ConfigGraph`.\n",
            "This codec is configuration-graph infrastructure, not a result of [AB09]; its "
            "conventions\n(the window `Turing.Cfg.InWindow` of radius `s`, the output summary) "
            "are those of\n`TCSlib.Complexity.SpaceComplexity.ConfigGraph`.\n", 1, "Word doc window")
    log("  module docstring: the InWin bullet removed; the window named `Turing.Cfg.InWindow`")
    t = dels(t, ["InWin"], log, "Word")
    t = lib.d1_rewrite(t, 7, 0, "Word")
    log("  D1: 7 code uses `InWin N r c` -> `Cfg.InWindow r c`")
    t = sub(t, '''    · have h1 : C.workTapes i z = none := by
        by_contra hne; exact hz ((hC i).2 z hne)
      have h2 : D.workTapes i z = none := by
        by_contra hne; exact hz ((hD i).2 z hne)
      rw [h1, h2]
  · funext i
    exact ((tape i _ (hC i).1).2.mp rfl).symm
''', '''    · have h1 : C.workTapes i z = none := hC.2 i z (not_le.mp hz)
      have h2 : D.workTapes i z = none := hD.2 i z (not_le.mp hz)
      rw [h1, h2]
  · funext i
    exact ((tape i _ (hC.1 i)).2.mp rfl).symm
''', 1, "Word coreSum_eq_of_cfgWord_eq")
    log("  coreSum_eq_of_cfgWord_eq: the window's two clauses read directly")
    return t


# ============================================================================ D1: Codec/Valid

def e_Valid(t, log):
    t = lib.d1_rewrite(t, 3, 0, "Valid")
    log("  D1: 3 code uses")
    t = sub(t, '''  refine ⟨fun i => ⟨?_, fun z hz => ?_⟩, fun j hj => ?_⟩
  · obtain ⟨j, hj, -, e⟩ := hpos i
    rw [e, abs_le]; constructor <;> omega
  · simp only [mkCfg] at hz
    by_contra hzs
    exact hz (if_neg hzs)
''', '''  refine ⟨⟨fun i => ?_, fun i z hz => ?_⟩, fun j hj => ?_⟩
  · obtain ⟨j, hj, -, e⟩ := hpos i
    rw [e, abs_le]; constructor <;> omega
  · simp only [mkCfg]
    exact if_neg (not_le.mpr hz)
''', 1, "Valid cellOf_mkCfg")
    t = sub(t, "    have := (hC i).1\n", "    have := hC.1 i\n", 1, "Valid vScan_cfgWord")
    log("  cellOf_mkCfg, vScan_cfgWord: proofs for the window's two clauses")
    return t


# ============================================================================ D1: Codec/Step

def e_Step(t, log):
    t = lib.d1_rewrite(t, 7, 0, "Step")
    log("  D1: 7 code uses")
    t = sub(t, "  · have hp := (hC i).1\n    rw [abs_le] at hp\n    simp only [Action.apply, "
            "signType_cast]\n    cases hm : (a.workTapes i).2 with\n    | zero => simp\n",
            "  · have hp := hC.1 i\n    rw [abs_le] at hp\n    simp only [Action.apply, "
            "signType_cast]\n    cases hm : (a.workTapes i).2 with\n    | zero => simp\n",
            1, "Step cellOf_apply")
    t = sub(t, '''  · rintro ⟨hl, hr⟩ i
    have hp := (hC i).1
    rw [abs_le] at hp
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Action.apply, signType_cast]
      cases hm : (a.workTapes i).2 with
      | zero => simp; rw [abs_le]; omega
      | pos => have := hr i hm; simp; rw [abs_le]; constructor <;> omega
      | neg => have := hl i hm; simp; rw [abs_le]; constructor <;> omega
    · simp only [Action.apply] at hz
      cases hw : (a.workTapes i).1 with
      | none => rw [hw] at hz; exact (hC i).2 z hz
      | some w =>
        rw [hw] at hz
        dsimp only at hz
        by_cases hzp : z = C.workTapePos i
        · rw [hzp, abs_le]; exact hp
        · rw [Function.update_of_ne hzp] at hz; exact (hC i).2 z hz
''', '''  · rintro ⟨hl, hr⟩
    refine ⟨fun i => ?_, fun i z hz => ?_⟩
    · have hp := hC.1 i
      rw [abs_le] at hp
      simp only [Action.apply, signType_cast]
      cases hm : (a.workTapes i).2 with
      | zero => simp; rw [abs_le]; omega
      | pos => have := hr i hm; simp; rw [abs_le]; constructor <;> omega
      | neg => have := hl i hm; simp; rw [abs_le]; constructor <;> omega
    · have hp := hC.1 i
      simp only [Action.apply]
      cases hw : (a.workTapes i).1 with
      | none => exact hC.2 i z hz
      | some w =>
        dsimp only
        have hzp : z ≠ C.workTapePos i := by
          rintro rfl; exact absurd hp (not_le.mpr hz)
        rw [Function.update_of_ne hzp]; exact hC.2 i z hz
''', 1, "Step boundary_iff forward")
    t = sub(t, "    · have := (hW i).1\n", "    · have := hW.1 i\n", 2, "Step boundary_iff backward")
    log("  cellOf_apply, boundary_iff: proofs for the window's two clauses")
    return t


# ============================================================================ D1: Codec/Langs

def e_Langs(t, log):
    t = lib.d1_rewrite(t, 8, 0, "Langs")
    log("  D1: 8 code uses (the three language definitions and their membership lemmas)")
    return t


# ============================================================================ D1: Codec/Checks

def e_Checks(t, log):
    t = dels(t, ["outSummary_eq_empty_iff"], log, "Checks")
    log("  (G-outsum: the lemma now lives beside `Turing.outSummary_eq_accept_iff` in ConfigGraph;"
        " the one use resolves to it through `open Turing`)")
    t = lib.d1_rewrite(t, 5, 0, "Checks")
    log("  D1: 5 code uses")
    t = sub(t, "  have hWin : Cfg.InWindow s (N.tm.initCfg x) := fun i => by simp [NDTM.initCfg, "
            "Cfg.init]\n", "  have hWin : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s\n",
            1, "Checks hWin")
    t = sub(t, "      · by_contra hne; exact hz ((hC i).2 z hne)\n",
            "      · exact hC.2 i z (not_le.mp hz)\n", 1, "Checks hblank")
    log("  initChk_iff: the initial window is `Turing.Cfg.inWindow_init`; the blank-outside clause read"
        " directly")
    return t


# ============================================================================ D1, D2, D2h, D3: Codec/Bridge

BRIDGE_DISCLOSURE_OLD = '''**Duplication disclosure.** The window lemma `Complexity.Codec.inWin_runWith_take` restates
the private `runWith_take_inWindow` of `TCSlib.Complexity.SpaceComplexity.ConfigGraph` for
the codec's public window predicate; its proof replays the private helpers there
(`take_succ_action`, `abs_lt_card_visitedWith`, `mem_visitedWith_of_ne_none`,
`visitedWith_take_subset`). The window predicate `Complexity.Codec.InWin` (Word.lean) is a
public copy of the private `InWindow` there, and `mem_of_acceptsWithin` replays the backward
branch of `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound`. Public exports from
`ConfigGraph` (`InWindow`, `runWith_take_inWindow`, an "accepting branch of any length implies
membership" lemma) are requested, after which these copies are deleted. Within the codec, the
path-to-membership argument exists once (`mem_of_codePath`); `mem_iff_codeChain` and the
Savitch machine (`Complexity.LogProg.SavitchARM.mem_iff_reach`) both use it.
'''
BRIDGE_DISCLOSURE_NEW = '''The window of a space-bounded branch and the step "an accepting branch of any length gives
membership" are those of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`
(`Turing.NDTM.runWith_take_inWindow`, `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`),
over the window predicate `Turing.Cfg.InWindow`. Within the codec, the path-to-membership
argument exists once (`mem_of_codePath`); `mem_iff_codeChain` and the Savitch machine
(`Complexity.LogProg.SavitchARM.mem_iff_reach`) both use it.
'''
BRIDGE_DELETE = ["take_succ_action", "abs_lt_card_visitedWith", "mem_visitedWith_of_ne_none",
                 "visitedWith_take_subset", "inWin_runWith_take", "mem_of_acceptsWithin"]


def e_Bridge(t, log):
    t = sub(t, BRIDGE_DISCLOSURE_OLD, BRIDGE_DISCLOSURE_NEW, 1, "Bridge disclosure")
    t = sub(t, "* `Complexity.Codec.configBound_mono`, `Complexity.Codec.mem_of_acceptsWithin` — "
            "helpers.\n* `Complexity.Codec.inWin_runWith_take` — prefixes of a space-bounded branch "
            "are in the\n  window.\n", "* `Complexity.Codec.configBound_mono` — a helper.\n", 1,
            "Bridge doc results")
    log("  module docstring: the duplication disclosure replaced by the citations; two Main "
        "results entries removed")
    t = dels(t, BRIDGE_DELETE, log, "Bridge")
    t = sub(t, "/-! ## Windows of space-bounded branches -/\n\n", "", 1, "Bridge empty section")
    log("  the emptied section header removed")
    t = lib.d1_rewrite(t, 2, 0, "Bridge")
    log("  D1: 2 code uses")
    t = sub(t, "      exact ⟨[], N.tm.initCfg x, fun i => by simp [NDTM.initCfg, Cfg.init], hinit, "
            "rfl⟩\n", "      exact ⟨[], N.tm.initCfg x, Cfg.inWindow_init _ x s, hinit, rfl⟩\n", 1,
            "Bridge init window")
    t = sub(t, "  apply mem_of_acceptsWithin h (t := w.length)\n",
            "  apply h.mem_of_acceptsWithin (t := w.length)\n", 1, "Bridge mem_of_codePath")
    t = sub(t, "accepting branch of any length gives membership (`mem_of_acceptsWithin`). -/",
            "accepting branch of any length gives membership\n"
            "(`Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`). -/", 1, "Bridge sketch")
    t = sub(t, "the window `[-s, s]` (`inWin_runWith_take`: compare", "the window `[-s, s]` "
            "(`Turing.NDTM.runWith_take_inWindow`: compare", 1, "Bridge codeChain sketch")
    t = sub(t, "inWin_runWith_take ", "NDTM.runWith_take_inWindow N.tm ", 4, "Bridge re-point")
    log("  mem_of_codePath -> `h.mem_of_acceptsWithin`; mem_iff_codeChain's 4 window uses -> "
        "`NDTM.runWith_take_inWindow N.tm`; the initial window -> `Cfg.inWindow_init`")
    return t


# ============================================================================ D1, D2, D5: ExpBFS/Radius

def e_Radius(t, log):
    t = dels(t, ["inWin_of_coreSum_eq"], log, "Radius")
    t = lib.d1_rewrite(t, 12, 0, "Radius")
    log("  D1: 12 code uses")
    t = sub(t, '''    Cfg.InWindow s' C := fun i =>
  ⟨(h i).1.trans (by exact_mod_cast hs), fun z hz => ((h i).2 z hz).trans (by exact_mod_cast hs)⟩
''', '''    Cfg.InWindow s' C :=
  ⟨fun i => (h.1 i).trans (by exact_mod_cast hs),
    fun i z hz => h.2 i z (lt_of_le_of_lt (by exact_mod_cast hs) hz)⟩
''', 1, "Radius inWin_mono")
    t = sub(t, '''  | some q =>
    intro i
    obtain ⟨hp, hz⟩ := h i
    have hmove := workTapePos_apply_le (N.tm.tr b q C.inputSymbol C.workTapeSymbols) C i
    refine ⟨by push_cast; rw [abs_le] at hp hmove ⊢; constructor <;> linarith [hp.1, hp.2,
      hmove.1, hmove.2], fun z hz' => ?_⟩
    rcases hwr : ((N.tm.tr b q C.inputSymbol C.workTapeSymbols).workTapes i).1 with _ | sym
    · simp only [Action.apply, hwr] at hz'
      exact (hz z hz').trans (by push_cast; linarith)
    · simp only [Action.apply, hwr] at hz'
      by_cases hzp : z = C.workTapePos i
      · subst hzp; exact hp.trans (by push_cast; linarith)
      · rw [Function.update_of_ne hzp] at hz'
        exact (hz z hz').trans (by push_cast; linarith)
''', '''  | some q =>
    refine ⟨fun i => ?_, fun i z hz' => ?_⟩
    · have hp := h.1 i
      have hmove := workTapePos_apply_le (N.tm.tr b q C.inputSymbol C.workTapeSymbols) C i
      push_cast; rw [abs_le] at hp hmove ⊢; constructor <;> linarith [hp.1, hp.2,
        hmove.1, hmove.2]
    · have hp := h.1 i
      have hzs : (s : ℤ) < |z| := by push_cast at hz'; linarith
      rcases hwr : ((N.tm.tr b q C.inputSymbol C.workTapeSymbols).workTapes i).1 with _ | sym
      · simp only [Action.apply, hwr]
        exact h.2 i z hzs
      · simp only [Action.apply, hwr]
        have hzp : z ≠ C.workTapePos i := by
          rintro rfl; exact absurd hp (not_le.mpr hzs)
        rw [Function.update_of_ne hzp]
        exact h.2 i z hzs
''', 1, "Radius inWin_stepWith")
    t = sub(t, "lemma inWin_init (s : ℕ) : Cfg.InWindow s (N.tm.initCfg x) := fun i => by\n"
            "  simp [NDTM.initCfg, Cfg.init]\n",
            "lemma inWin_init (s : ℕ) : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s\n",
            1, "Radius inWin_init")
    log("  inWin_mono, inWin_stepWith, inWin_init: proofs for the window's two clauses")
    t = sub(t, "      refine ⟨w ++ [b], hw.snoc b (inWin_of_coreSum_eq hv'.symm hC'), ?_⟩\n",
            "      refine ⟨w ++ [b], hw.snoc b (NDTM.inWindow_of_coreSum_eq hv' hC'), ?_⟩\n", 1,
            "Radius rcode_iff")
    t = sub(t, '''    exact inWin_of_coreSum_eq (coreSum_eq_of_code_eq ((hw'.mono (by omega)).last) hstep hre)
      hw'.last
''', '''    exact NDTM.inWindow_of_coreSum_eq
      (coreSum_eq_of_code_eq ((hw'.mono (by omega)).last) hstep hre).symm hw'.last
''', 1, "Radius winRun_of_card_eq")
    t = sub(t, "still in the window (`inWin_of_coreSum_eq`). -/",
            "still in the window (`Turing.NDTM.inWindow_of_coreSum_eq`). -/", 1, "Radius sketch 1")
    log("  rcode_iff, winRun_of_card_eq -> `NDTM.inWindow_of_coreSum_eq` (its vertex equation is the"
        " other way round)")
    t = sub(t, "prefixes are in the window (`Complexity.Codec.inWin_runWith_take`); a shorter word",
            "prefixes are in the window (`Turing.NDTM.runWith_take_inWindow`); a shorter word", 1,
            "Radius sketch 2")
    t = sub(t, "    have := inWin_runWith_take w' (hSpace w' hw') w.length\n",
            "    have := NDTM.runWith_take_inWindow N.tm w' (hSpace w' hw') w.length\n", 1, "Radius 1")
    t = sub(t, "    have := inWin_runWith_take (w.take T) (hSpace _ hlen) T\n",
            "    have := NDTM.runWith_take_inWindow N.tm (w.take T) (hSpace _ hlen) T\n", 1, "Radius 2")
    log("  inWin_runWith_of_decides -> `NDTM.runWith_take_inWindow`")
    return t


# ============================================================================ metadata

# key -> (path, edit function name, kind): kind "code" (code changes) or "comment" (comments
# and docstrings only; asserted by land.py through the code-identity normal form)
FILES = {}


def reg(key, rel, kind):
    FILES[key] = (rel, "e_" + key, kind)


reg("ConfigGraph", SC + "ConfigGraph.lean", "code")
reg("Word", SC + "Codec/Word.lean", "code")
reg("Valid", SC + "Codec/Valid.lean", "code")
reg("Step", SC + "Codec/Step.lean", "code")
reg("Langs", SC + "Codec/Langs.lean", "code")
reg("Checks", SC + "Codec/Checks.lean", "code")
reg("Bridge", SC + "Codec/Bridge.lean", "code")
reg("Radius", SC + "ExpBFS/Radius.lean", "code")

# the D1-restated modules: their public statements change, so every module downstream of one
# of them is inlined into a cut rather than loaded from the snapshot
RESTATED = ["Word", "Valid", "Step", "Langs", "Checks", "Bridge", "Radius"]

# additive deltas of changed modules that are not inlined: (opening text, declarations, closing
# text) groups whose declarations are copied from the landed file; plus new imports
CG_CTX = ("namespace Turing\n\nvariable {k : ℕ} {S : Type} {x : List Bool}\n\n", "end Turing\n")
DELTAS = {
    "ConfigGraph": {"imports": [], "groups": [
        (CG_CTX[0], ["outSummary_eq_empty_iff", "Cfg.InWindow.core_bounds"], CG_CTX[1]),
        (CG_CTX[0] + "namespace NDTM\n\n", CG_PROMOTE, "end NDTM\n\n" + CG_CTX[1]),
        (CG_CTX[0] + "namespace FinNDTM\n\n", ["DecidesInSpace.mem_of_acceptsWithin"],
         "end FinNDTM\n\n" + CG_CTX[1]),
    ]},
}


# ============================================================================ InputAccess (ours)

IA_INDICATORS = '''/-- **The bit language answers with the indexed letter**: on a genuine pair `⟨y, bits a⟩` the
indicator of `Complexity.inputBitLang` is letter `a` of `y` (`false` beyond the end).

**Proof sketch.** `Complexity.indicator_indexLang_pairEncode`, by cases on the letter. -/
theorem indicator_inputBitLang (y : List Bool) (a : ℕ) :
    MultiTapeTM.indicator (inputBitLang : Set (List Bool)) (pairEncode y (Nat.bits a)) =
      y.getD a false := by
  rw [inputBitLang, indicator_indexLang_pairEncode]
  cases y.getD a false <;> simp

/-- **The length language answers with the comparison**: on a genuine pair `⟨y, bits a⟩` the
indicator of `Complexity.inputLenLang` decides `a < |y|`.

**Proof sketch.** `Complexity.indicator_indexLang_pairEncode`. -/
theorem indicator_inputLenLang (y : List Bool) (a : ℕ) :
    MultiTapeTM.indicator (inputLenLang : Set (List Bool)) (pairEncode y (Nat.bits a)) =
      decide (a < y.length) := by
  rw [inputLenLang, indicator_indexLang_pairEncode]
  exact decide_eq_decide.mpr Iff.rfl
'''

IA_CHAIN = '''/-- **A bounded straight chain of unit steps of one register**: if the instructions at the
labels `labels 0, …, labels (k - 1)` all increment register `r` (`up = true`), or all decrement
it (`up = false`), each passing to the next label, then the run from `labels 0` reaches
`labels k` with `r` raised (respectively lowered) by `k`, every register staying at most `B`.
The side condition is `v r + k ≤ B` for increments and `k ≤ v r` for decrements, so that no
decrement truncates. The labels may belong to any larger ARM; no new reachability relation is
needed. The increment chains of the bounded fragments below and the codec's chains
(`Complexity.Codec.incChain`, `Complexity.Codec.decChain`) are its instances.

**Proof sketch.** Induction on `k`. A step at `labels 0` moves `r` by one, within the bound;
the rest of the chain starts at `labels 1`. -/
theorem arm_chain {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (r : Fin m) (up : Bool)
    (labels : ℕ → Λ) (k B : ℕ)
    (hcode : ∀ i < k, A (labels i) =
      bif up then .inc r (labels (i + 1)) else .dec r (labels (i + 1)))
    (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B) (hk : bif up then v r + k ≤ B else k ≤ v r) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
      (some (labels 0), v, none)
      (some (labels k), Function.update v r (bif up then v r + k else v r - k), none) := by
  induction k generalizing labels v with
  | zero =>
    have e : (bif up then v r + 0 else v r - 0) = v r := by cases up <;> rfl
    rw [e, Function.update_eq_self]
    exact AReach.refl _
  | succ k ih =>
    have hc := hcode 0 (by omega)
    let v' := Function.update v r (bif up then v r + 1 else v r - 1)
    have hv' : ∀ s, v' s ≤ B := by
      intro s
      by_cases hs : s = r
      · subst s
        have := hv r
        cases up <;> simp only [cond_true, cond_false] at hk <;> simp [v'] <;> omega
      · simpa [v', Function.update_of_ne hs] using hv s
    have hpre : PreS A x (some (labels 0), v, none) := by cases up <;> simp [PreS, hc]
    have hstep : astep A oracle x (some (labels 0), v, none) = (some (labels 1), v', none) := by
      cases up <;> simp [astep, hc, v']
    have hp := ih (fun i => labels (i + 1)) (fun i hi => hcode (i + 1) (by omega)) v' hv'
      (by cases up <;> simp only [cond_true, cond_false, v', Function.update_self] at hk ⊢ <;>
        omega)
    have e : Function.update v' r (bif up then v' r + k else v' r - k) =
        Function.update v r (bif up then v r + (k + 1) else v r - (k + 1)) := by
      cases up <;> simp only [cond_true, cond_false, v', Function.update_self,
        Function.update_idem] <;> congr 1 <;> omega
    apply AReach.step ⟨hpre, hv⟩
    rw [hstep]
    rw [e] at hp
    exact hp
'''

IA_STRIDE = '''/-- **The stride decoder**: a strided reverse scan decodes a bounded binary field laid out at
positions `base + stride · i` (least significant letter first). From the pointer at
`base + stride · k`, with the suffix value from letter `k` in the accumulator, the run reaches
`done` with the value of the whole field; it reads only positions in that field, and only the
pointer, the accumulator and the temporary change. The caller supplies bounds for the suffix
values, after its width check. `boundedDecode_loop` is the case `stride = 1`, and the codec's
`Complexity.Codec.decodeStride_loop` the general one.

**Proof sketch.** Induction on `k`. At `k = 0` the pointer is at the base and the run exits.
Otherwise step the pointer down by `stride` (`arm_chain`), read letter `k - 1`, copy the
accumulator into the temporary (`registerCopy_loop`), clear the accumulator, transfer twice
the temporary back (`registerScale_loop`), and add the letter: the accumulator holds the
suffix value from `k - 1`. The suffix-value equation bounds both the doubled value and the
final increment. -/
theorem boundedDecodeStride_loop {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (ptr base acc tmp : Fin m)
    (hpb : ptr ≠ base) (hpa : ptr ≠ acc) (hpt : ptr ≠ tmp)
    (hba : base ≠ acc) (hbt : base ≠ tmp) (hat : acc ≠ tmp)
    (j : Fin d) (test read done : Λ) (downs : ℕ → Λ)
    (copy bump clear scale take add : Bool → Λ) (incs : Bool → ℕ → Λ) (stride : ℕ)
    (htest : A test = .jeq ptr base done (downs 0))
    (hdowns : ∀ i < stride, A (downs i) = .dec ptr (downs (i + 1)))
    (hdend : downs stride = read)
    (hread : A read = .call j .whole [ptr] (copy true) (copy false))
    (hcopy : ∀ b, A (copy b) = .jeq tmp acc (clear b) (bump b))
    (hbump : ∀ b, A (bump b) = .inc tmp (copy b))
    (hclear : ∀ b, A (clear b) = .clr acc (scale b))
    (hscale : ∀ b, A (scale b) = .jz tmp (add b) (take b))
    (htake : ∀ b, A (take b) = .dec tmp (incs b 0))
    (hincs : ∀ b i, i < 2 → A (incs b i) = .inc acc (incs b (i + 1)))
    (hend : ∀ b, incs b 2 = scale b)
    (hadd : ∀ b, A (add b) = if b then .inc acc test else .jz tmp test test)
    (w : List Bool) (B : ℕ) (values : ∀ i ≤ w.length, bitsVal (w.drop i) ≤ B)
    (k : ℕ) (hk : k ≤ w.length) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hs : 0 < stride)
    (hp : v ptr = v base + stride * k) (ha : v acc = bitsVal (w.drop k)) (ht : v tmp = 0)
    (ho : ∀ i < w.length,
      oracle j (pairEncode x (Nat.bits (v base + stride * i))) = w.getD i false) :
    ∃ v', (∀ r, v' r ≤ B) ∧ v' ptr = v base ∧ v' acc = bitsVal w ∧ v' tmp = 0 ∧
      (∀ r, r ≠ ptr → r ≠ acc → r ≠ tmp → v' r = v r) ∧
      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none) (some done, v', none) := by
  induction k generalizing v with
  | zero =>
    have eq : v ptr = v base := by simpa using hp
    refine ⟨v, hv, eq, by simpa using ha, ht, fun _ _ _ _ => rfl, ?_⟩
    simpa [astep, htest, eq] using
      (AReach.single (A := A) (oracle := oracle) (x := x)
        (a := (some test, v, none)) ⟨by simp [PreS, htest, hpb], hv⟩)
  | succ k ih =>
    have kin : k < w.length := by omega
    let b := w.getD k false
    have val : bitsVal (w.drop k) = b.toNat + 2 * bitsVal (w.drop (k + 1)) := by
      rw [List.drop_eq_getElem_cons kin]
      simp only [bitsVal]
      congr 1
      simp [b, List.getD_eq_getElem?_getD, kin]
    have bound : 2 * v acc + b.toNat ≤ B := by
      have vb := values k (by omega)
      rw [val, ← ha] at vb
      omega
    let vd := Function.update v ptr (v base + stride * k)
    let vc := Function.update vd tmp (v acc)
    let vz := Function.update vc acc 0
    let vs := Function.update (Function.update vz tmp 0) acc (2 * v acc)
    let vn := Function.update vs acc (bitsVal (w.drop k))
    have bd : ∀ r, vd r ≤ B := register_update_le v ptr B _ hv (by
      have := hv ptr; rw [hp, Nat.mul_succ] at this; omega)
    have bc : ∀ r, vc r ≤ B := register_update_le vd tmp B _ bd (hv acc)
    have bz : ∀ r, vz r ≤ B := register_update_le vc acc B 0 bc (Nat.zero_le _)
    have bs : ∀ r, vs r ≤ B := register_update_le _ acc B _
      (register_update_le vz tmp B 0 bz (Nat.zero_le _)) (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le vs acc B _ bs (values k (by omega))
    have vb : vn base = v base := by simp [vn, vs, vz, vc, vd, hba, hbt, hpb.symm]
    have vp : vn ptr = v base + stride * k := by simp [vn, vs, vz, vc, vd, hpa, hpt]
    have va : vn acc = bitsVal (w.drop k) := by simp [vn]
    have vt : vn tmp = 0 := by simp [vn, vs, hat.symm]
    have vf : ∀ r, r ≠ ptr → r ≠ acc → r ≠ tmp → vn r = v r := by
      intro r hr hp ht
      simp [vn, vs, vz, vc, vd, Function.update_of_ne, hr, hp, ht]
    obtain ⟨v', bv, ep, ea, et, frame, rest⟩ := ih (by omega) vn bn
      (by rw [vp, vb]) va vt (by simpa only [vb] using ho)
    refine ⟨v', bv, by simpa only [vb] using ep, ea, et, ?_, ?_⟩
    · intro r hr hp ht
      exact (frame r hr hp ht).trans (vf r hr hp ht)
    · have ne : v ptr ≠ v base := by rw [hp, Nat.mul_succ]; omega
      apply AReach.step ⟨by simp [PreS, htest, hpb], hv⟩
      simp only [astep, htest, if_neg ne]
      have dc : AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
          (some (downs 0), v, none)
          (some (downs stride), Function.update v ptr (v ptr - stride), none) :=
        arm_chain A oracle x ptr false downs stride B hdowns v hv
          (by show stride ≤ v ptr; rw [hp, Nat.mul_succ]; omega)
      have pred : v ptr - stride = v base + stride * k := by rw [hp, Nat.mul_succ]; omega
      rw [pred, hdend] at dc
      apply dc.trans
      change AReach A oracle x _ (some read, vd, none) _
      apply AReach.step ⟨by simp [PreS, hread], bd⟩
      have bit : oracle j (pairEncode x (Nat.bits (vd ptr))) = b := by
        simpa only [vd, Function.update_self] using ho k kin
      simp only [astep, hread, vword_whole₁, bit]
      have cb : (if b = true then copy true else copy false) = copy b := by cases b <;> rfl
      rw [cb]
      have cr := registerCopy_loop A oracle x tmp acc hat.symm (copy b) (bump b) (clear b)
        (hcopy b) (hbump b) B vd bd (by simp [vd, hpt.symm, hpa.symm, ht])
      have ca : vd acc = v acc := by simp [vd, hpa.symm]
      simp only [ca] at cr
      apply cr.trans
      change AReach A oracle x _ (some (clear b), vc, none) _
      apply AReach.step ⟨by simp [PreS, hclear], bc⟩
      simp only [astep, hclear]
      change AReach A oracle x _ (some (scale b), vz, none) _
      have za : vz acc = 0 := by simp [vz]
      have zt : vz tmp = v acc := by simp [vz, vc, hat.symm]
      have sr := registerScale_loop A oracle x tmp acc hat.symm (scale b) (take b) (add b)
        (incs b) 2 (hscale b) (htake b) (hincs b) (hend b) B vz bz
        (by rw [za, zt]; omega)
      simp only [za, zt, Nat.zero_add] at sr
      apply sr.trans
      change AReach A oracle x _ (some (add b), vs, none) _
      apply AReach.step ⟨by cases b <;> simp [PreS, hadd], bs⟩
      have nb : astep A oracle x (some (add b), vs, none) = (some test, vn, none) := by
        have sv : vs acc = 2 * v acc := by simp [vs]
        have kv : bitsVal (w.drop k) = b.toNat + 2 * v acc := by rw [val, ← ha]
        cases hb : b
        · have same : vn = vs := by
            simp only [vn, kv, hb, Bool.toNat_false, Nat.zero_add, ← sv, Function.update_eq_self]
          simp [astep, hadd, same]
        · simp only [astep, hadd, ↓reduceIte]
          simp only [vn, kv, hb, Bool.toNat_true, sv, Nat.add_comm]
      rw [nb]
      exact rest
'''

IA_CANON = '''/-- **The canonicality flag is `Canon`**: the last letter of a word, read with default `true`,
is `true` exactly when the word is canonical (`Canon`: empty, or ending in `1`). It is the
flag the tail loop `canonicalTail_loop` remembers.

**Proof sketch.** The empty word has flag `true` and is canonical; otherwise the flag is the
last letter. -/
theorem drop_canon (w : List Bool) : w.getLastD true = true ↔ Canon w := by
  by_cases hw : w = []
  · subst w; simp [Canon]
  · simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some, Canon]
    exact ⟨fun h _ => h, fun h => h hw⟩
'''

IA_BD_OLD_PROOF_HEAD = '''      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none) (some done, v', none) := by
  induction k generalizing v with
  | zero =>
    have eq : v ptr = v base := by simpa using hp
'''


IA_PAIR_SND = """/-- **A letter of the second field of a pair**: letter `j` of `v` sits at position
`2 |u| + 2 + j` of `⟨u, v⟩` (reading with default `false`, also beyond the end).

**Proof sketch.** The address lies past the doubled first field and the separator, so the last
case of `pairEncode_getD` reads letter `j` of `v`. -/
theorem pairEncode_getD_snd (u v : List Bool) (j : ℕ) :
    (pairEncode u v).getD (2 * u.length + 2 + j) false = v.getD j false := by
  rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega
"""


def e_InputAccess(t, log):
    # G-oracle: the public forms of the bit and length oracle answers
    t = sub(t, "def inputLenLang : Language Bool := indexLang fun u i => i < u.length\n\n",
            "def inputLenLang : Language Bool := indexLang fun u i => i < u.length\n\n"
            + IA_INDICATORS + "\n", 1, "IA indicators")
    log("  insert indicator_inputBitLang, indicator_inputLenLang after inputLenLang (G-oracle)")
    d0, s0, e0, ls = lib.locate(t, "pairEncode_getD", TMP)
    t = "\n".join(ls[:e0 + 1] + [""] + IA_PAIR_SND.rstrip("\n").split("\n") + ls[e0 + 1:])
    log(f"  insert pairEncode_getD_snd after pairEncode_getD (base line {s0 + 1}; G-pairidx, user "
        "2026-10-14)")
    # D7: the parameterized chain lemma; arm_increments its instance
    d0, s0, e0, ls = lib.locate(t, "arm_increments", TMP)
    old = "\n".join(ls[d0:e0 + 1])
    new_inc = '''/-- A bounded straight sequence of register increments (`arm_chain` with `up = true`). The
labels may belong to any larger ARM; no new reachability relation is needed. -/
private lemma arm_increments {m d : ℕ} {Λ : Type} (A : ARM m d Λ)
    (oracle : Fin d → List Bool → Bool) (x : List Bool) (r : Fin m)
    (labels : ℕ → Λ) (k B : ℕ)
    (hcode : ∀ i < k, A (labels i) = .inc r (labels (i + 1)))
    (v : Fin m → ℕ) (hv : ∀ s, v s ≤ B) (hk : v r + k ≤ B) :
    AReach A oracle x (fun a => PreS A x a ∧ ∀ s, a.2.1 s ≤ B)
      (some (labels 0), v, none)
      (some (labels k), Function.update v r (v r + k), none) :=
  arm_chain A oracle x r true labels k B hcode v hv hk'''
    t = sub(t, old, IA_CHAIN + "\n" + new_inc, 1, "IA arm_chain")
    log(f"  insert arm_chain before arm_increments (base line {s0 + 1}); arm_increments its "
        "`up = true` instance")
    # L049: access_width_half public
    t = pub(t, ["access_width_half"], log)
    t = sub(t, "/-- Halving a nonzero cap removes exactly one binary digit. -/\n",
            "/-- **Halving a nonzero number removes exactly one binary digit**:\n"
            "`|bits (n / 2)| + 1 = |bits n|` for `n ≠ 0`.\n\n**Proof sketch.** `bits (n / 2)` is "
            "the tail of `bits n` (`bits_half`), which is nonempty. -/\n", 1, "IA width doc")
    # G-canon: the canonicality flag, moved down from QueryReshape, public
    d0, s0, e0, ls = lib.locate(t, "access_width_half", TMP)
    t = "\n".join(ls[:e0 + 1] + [""] + IA_CANON.rstrip("\n").split("\n") + ls[e0 + 1:])
    log("  insert drop_canon after access_width_half (G-canon: moved from QueryReshape, public)")
    # D7: the stride decoder; boundedDecode_loop its `stride = 1` instance
    d0, s0, e0, ls = lib.locate(t, "boundedDecode_loop", TMP)
    old = "\n".join(ls[d0:e0 + 1])
    head = old[:old.index(IA_BD_OLD_PROOF_HEAD)]
    head = sub(head, '''**Proof sketch.** At the boundary with `k` letters still unread, the accumulator is the
value of the suffix starting at `k`. Decrement the pointer, read letter `k-1`, copy the
accumulator into the temporary, clear the accumulator, and transfer twice the temporary
back. Add the letter and recur. The suffix-value equation bounds both the doubled value
and the final increment. Copying and scaling cite their shared ARM fragments. -/''',
               '''**Proof sketch.** The stride decoder `boundedDecodeStride_loop` at stride `1`, the single
decrement as a one-step chain. -/''', 1, "IA bd sketch")
    new_bd = head + '''      AReach A oracle x (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ B)
        (some test, v, none) (some done, v', none) :=
  boundedDecodeStride_loop A oracle x ptr base acc tmp hpb hpa hpt hba hbt hat j test read done
    (fun i => if i = 0 then down else read) copy bump clear scale take add incs 1
    (by simpa using htest)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using hdown)
    (by simp) hread hcopy hbump hclear hscale htake hincs hend hadd w B values k hk v hv
    Nat.one_pos (by simpa using hp) ha ht (by simpa using ho)'''
    t = sub(t, old, IA_STRIDE + "\n" + new_bd, 1, "IA stride")
    log(f"  insert boundedDecodeStride_loop before boundedDecode_loop (base line {s0 + 1}); "
        "boundedDecode_loop its `stride = 1` instance")
    t = sub(t, "* `Complexity.LogProg.boundedDecode_loop` — reverse binary decoding after the width "
            "check.\n", "* `Complexity.LogProg.boundedDecode_loop` — reverse binary decoding after the width "
            "check, the\n  unit-stride case of `Complexity.LogProg.boundedDecodeStride_loop`.\n"
            "* `Complexity.LogProg.arm_chain` — a bounded chain of increments or decrements of one "
            "register.\n* `Complexity.LogProg.access_width_half`, `Complexity.LogProg.drop_canon` — "
            "halving removes one binary\n  digit; the tail loop's flag is `Canon`.\n"
            "* `Complexity.indicator_inputBitLang`, `Complexity.indicator_inputLenLang` — the answers"
            " of the\n  bit and length languages on a genuine pair.\n"
            "* `Complexity.pairEncode_getD_snd` — a letter of the second field of a pair.\n", 1,
            "IA doc results")
    log("  module docstring: Main results entries for the new public declarations")
    return t


# ============================================================================ Codec/Engine

ENGINE_DISC_OLD = '''**Duplication disclosure.** `decodeStride_loop` is `boundedDecode_loop` of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` with its single decrement replaced
by a chain of `stride` decrements (the codec's fields are doubled in the virtual input); the
proof is adapted from that one. `incChain` is the public form of the private
`arm_increments` there. A shared generalization of both is requested.
'''
ENGINE_DISC_NEW = '''The chains and the stride decoder are those of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`: `incChain` and `decChain` are the two
directions of `Complexity.LogProg.arm_chain`, and `decodeStride_loop` is
`Complexity.LogProg.boundedDecodeStride_loop` (the codec's fields are doubled in the virtual
input, so it reads at stride two), all stated here through the guard `GuardLe`.
'''


def e_Engine(t, log):
    t = sub(t, ENGINE_DISC_OLD, ENGINE_DISC_NEW, 1, "Engine disclosure")
    log("  module docstring: the duplication disclosure replaced by the citations")
    # incChain, decChain: instances of arm_chain
    for name, up, doc_old, doc_new in (
            ("incChain", "true", "/-- **A chain of increments** of register `r` along the labels "
             "`labels 0, …, labels k`. -/\n", "/-- **A chain of increments** of register `r` along "
             "the labels `labels 0, …, labels k`.\n\n**Proof sketch.** `Complexity.LogProg.arm_chain`"
             " with `up = true`. -/\n"),
            ("decChain", "false", "(with `k ≤ v r`, so no decrement truncates). -/\n",
             "(with `k ≤ v r`, so no decrement truncates).\n\n**Proof sketch.** "
             "`Complexity.LogProg.arm_chain` with `up = false`. -/\n")):
        t = sub(t, doc_old, doc_new, 1, f"Engine {name} doc")
        d0, s0, e0, ls = lib.locate(t, name, TMP)
        decl = ls[s0:e0 + 1]
        k = next(i for i, l in enumerate(decl) if l.endswith(":= by"))
        decl = decl[:k] + [decl[k][:-len(" by")]] + \
            [f"  arm_chain A oracle y r {up} labels k B hcode v hv hk"]
        t = "\n".join(ls[:s0] + decl + ls[e0 + 1:])
        log(f"  {name}: proof -> `arm_chain A oracle y r {up} labels k B hcode v hv hk`")
    # decodeStride_loop: the stride decoder
    t = sub(t, '''(most significant letter last), the strided form of `boundedDecode_loop`.''',
            '''(most significant letter last), `boundedDecodeStride_loop`.''', 1, "Engine bullet")
    t = sub(t, '''reaches `done` with the value of the whole field. This is `boundedDecode_loop` of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` with the pointer stepped by
`stride` decrements (duplication disclosed in the module docstring).

**Proof sketch.** Induction on `k`. At `k = 0` the pointer is at the base and the run
exits. Otherwise step the pointer down by `stride` (`decChain`), read letter `k - 1`, copy
the accumulator into the temporary (`registerCopy_loop`), clear the accumulator, transfer
twice the temporary back (`registerScale_loop`), and add the letter: the accumulator holds
the suffix value from `k - 1`. -/''', '''reaches `done` with the value of the whole field.

**Proof sketch.** The stride decoder `Complexity.LogProg.boundedDecodeStride_loop` of
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess`, whose guard is `GuardLe`. -/''', 1,
            "Engine decode doc")
    d0, s0, e0, ls = lib.locate(t, "decodeStride_loop", TMP)
    decl = ls[s0:e0 + 1]
    k = next(i for i, l in enumerate(decl) if l.endswith(":= by"))
    decl = decl[:k] + [decl[k][:-len(" by")],
                       "  boundedDecodeStride_loop A oracle y ptr base acc tmp hpb hpa hpt hba hbt "
                       "hat j test read done",
                       "    downs copy bump clear scale take add incs stride htest hdowns hdend "
                       "hread hcopy hbump hclear",
                       "    hscale htake hincs hend hadd w B values k hk v hv hs hp ha ht ho"]
    t = "\n".join(ls[:s0] + decl + ls[e0 + 1:])
    log("  decodeStride_loop: proof -> `boundedDecodeStride_loop ...`")
    # L049: halvCount_loop cites access_width_half
    t = sub(t, '''      have hlen : (Nat.bits (n / 2)).length + 1 = (Nat.bits n).length := by
        rw [bits_half, List.length_tail]
        have : 0 < (Nat.bits n).length := by
          rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr hpos
        omega
''', '''      have hlen : (Nat.bits (n / 2)).length + 1 = (Nat.bits n).length :=
        access_width_half n (Nat.pos_iff_ne_zero.mp hpos)
''', 1, "Engine halvCount_loop")
    t = sub(t, "binary digit when halved (`bits_half`). -/",
            "binary digit when halved (`Complexity.LogProg.access_width_half`). -/", 1,
            "Engine halv sketch")
    log("  halvCount_loop: the halving width -> `access_width_half n (Nat.pos_iff_ne_zero.mp hpos)`"
        " (L049)")
    return t


# ============================================================================ QueryReshape (ours)

def e_QueryReshape(t, log):
    t = sub(t, '''    dropOracle 0 (pairEncode h (Nat.bits i)) = h.getD i false := by
  change MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  simp [inputBitLang, indicator_indexLang_pairEncode]
''', '''    dropOracle 0 (pairEncode h (Nat.bits i)) = h.getD i false := by
  change MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  exact indicator_inputBitLang h i
''', 1, "QR drop_bit")
    t = sub(t, '''    dropOracle 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) := by
  simp [dropOracle, dropBank, inputLenLang, indicator_indexLang_pairEncode]
''', '''    dropOracle 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) := by
  change MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact indicator_inputLenLang h i
''', 1, "QR drop_len")
    log("  drop_bit, drop_len: proofs cite `indicator_inputBitLang`, `indicator_inputLenLang`")
    t = sub(t, """  have div : (4 * x.length + 4 + 2 * j) / 2 = 2 * x.length + 2 + j := by omega
  rw [div, pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega
""", """  have div : (4 * x.length + 4 + 2 * j) / 2 = 2 * x.length + 2 + j := by omega
  rw [div, pairEncode_getD_snd]
""", 1, "QR comp_suffix_address")
    log("  comp_suffix_address: the inner second-field read cites `pairEncode_getD_snd` (G-pairidx, "
        "L052)")
    t = dels(t, ["drop_canon"], log, "QR")
    log("  (G-canon: drop_canon moved to InputAccess, public; its 5 uses resolve to it through"
        " `open LogProg`)")
    return t


# ============================================================================ G-oracle copies

def e_Run(t, log):
    for nm, old, new in (
            ("orc_bit", "  rw [inputBitLang, indicator_indexLang_pairEncode]\n"
             "  cases y.getD a false <;> simp\n", "  exact indicator_inputBitLang y a\n"),
            ("orc_len", "  rw [inputLenLang, indicator_indexLang_pairEncode]\n"
             "  exact decide_eq_decide.mpr Iff.rfl\n", "  exact indicator_inputLenLang y a\n")):
        t = sub(t, old, new, 1, f"Run {nm}")
        log(f"  {nm}: proof cites `{new.split()[1]}`")
    return t


e_TQBFARMMachine = e_Run


def e_Parse(t, log):
    t = sub(t, '''lemma canon_of_getLastD {w : List Bool} (h : w.getLastD true = true) : Canon w := by
  intro hw
  rwa [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some] at h
''', '''lemma canon_of_getLastD {w : List Bool} (h : w.getLastD true = true) : Canon w :=
  (drop_canon w).mp h
''', 1, "Parse canon_of_getLastD")
    t = sub(t, '''lemma getLastD_of_canon {w : List Bool} (h : Canon w) : w.getLastD true = true := by
  by_cases hw : w = []
  · rw [hw]; rfl
  · rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hw, Option.getD_some]
    exact h hw
''', '''lemma getLastD_of_canon {w : List Bool} (h : Canon w) : w.getLastD true = true :=
  (drop_canon w).mpr h
''', 1, "Parse getLastD_of_canon")
    log("  canon_of_getLastD, getLastD_of_canon: the two directions of `drop_canon` (G-canon)")
    t = sub(t, """    (pairEncode u v).getD (2 * u.length + 2 + j) false = v.getD j false := by
  rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega
""", """    (pairEncode u v).getD (2 * u.length + 2 + j) false = v.getD j false :=
  pairEncode_getD_snd u v j
""", 1, "Parse pe_getD_snd")
    log("  pe_getD_snd: proof -> `pairEncode_getD_snd u v j` (G-pairidx)")
    return t


def e_Mult(t, log):
    t = sub(t, """  · intro i hi
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 2 * a.length + 2 + 2 * i - 2 * a.length - 2 = 2 * i by omega]
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 2 * a.length + 2 + 2 * b.length + 2 + i - 2 * a.length - 2 =
      2 * b.length + 2 + i by omega]
    rw [pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
""", """  · intro i hi
    rw [pairEncode_getD_snd, pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i
    rw [show 2 * a.length + 2 + 2 * b.length + 2 + i = 2 * a.length + 2 + (2 * b.length + 2 + i)
      by omega, pairEncode_getD_snd, pairEncode_getD_snd]
""", 1, "Mult mult_addresses")
    log("  mult_addresses: the second-field reads cite `pairEncode_getD_snd` (G-pairidx, L050)")
    return t


def e_VWord(t, log):
    t = sub(t, "import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess\n",
            "import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess\n"
            "import TCSlib.Programs.Util.List\n", 1, "VWord import")
    t = sub(t, '''lemma getD_drop (y : List Bool) (a i : ℕ) : (y.drop a).getD i false = y.getD (a + i) false := by
  simp [List.getD_eq_getElem?_getD]
''', '''lemma getD_drop (y : List Bool) (a i : ℕ) : (y.drop a).getD i false = y.getD (a + i) false :=
  List.getD_drop y a i false
''', 1, "VWord getD_drop")
    t = sub(t, "* `Complexity.getD_drop` — the letters of a suffix `y.drop a` of the input are the "
            "letters\n  of `y` shifted by `a` (with default `false`); used by",
            "* `Complexity.getD_drop` — the letters of a suffix `y.drop a` of the input are the "
            "letters\n  of `y` shifted by `a` (with default `false`; the `Bool` case of the "
            "vendored\n  `List.getD_drop` of `TCSlib.Programs.Util.List`); used by", 1, "VWord doc")
    log("  import TCSlib.Programs.Util.List; getD_drop cites `List.getD_drop` (M2)")
    return t

reg("InputAccess", SC + "Logspace/InputAccess.lean", "code")
reg("Engine", SC + "Codec/Engine.lean", "code")
reg("QueryReshape", SC + "Logspace/QueryReshape.lean", "code")
reg("Run", SC + "Codec/Run.lean", "code")
reg("TQBFARMMachine", C + "ClassPSPACE/TQBFARM/Machine.lean", "code")
reg("Parse", SC + "Codec/Parse.lean", "code")
reg("VWord", SC + "Machines/VWord.lean", "code")
reg("Mult", SC + "Logspace/Mult.lean", "code")

IA_CTX = "namespace Complexity\n\nopen Turing\n\n"
DELTAS["InputAccess"] = {"imports": [], "groups": [
    (IA_CTX, ["pairEncode_getD_snd", "indicator_inputBitLang", "indicator_inputLenLang"],
     "end Complexity\n"),
    (IA_CTX + "namespace LogProg\n\nopen Classical\n\n",
     ["arm_chain", "access_width_half", "drop_canon", "boundedDecodeStride_loop"],
     "end LogProg\n\nend Complexity\n"),
]}
DELTAS["VWord"] = {"imports": ["TCSlib.Programs.Util.List"], "groups": []}


# ============================================================================ D4 (user exception)

def e_DAGCircuitSat(t, log):
    t = pub(t, ["eval_tseitinGates_values", "values_getD_eq_of_eval_tseitinGates"], log)
    log("  (D4, as extended by the user on 2026-10-14: two visibility changes, no other edit in "
        "this file)")
    return t


def e_TQBFHardTseitin(t, log):
    t = sub(t, '''      refine ⟨by simpa [CNF.Clause.eval, DAGCircuit.eval] using h, ?_⟩
      rw [eval_tseitinGates]
      intro i hi
      rw [DAGGate.eval_tseitin _ _ (hC _ (List.getElem_mem hi)) _ (C.values fun i => σ i)
        (fun _ _ => rfl)]
      exact C.values_getD_gate _ hi
''', '''      exact ⟨by simpa [CNF.Clause.eval, DAGCircuit.eval] using h,
        DAGCircuit.eval_tseitinGates_values C hC (fun i => σ i)⟩
''', 1, "Tseitin toCNF_extension_iff")
    t = sub(t, '''(`values_getD_input`), each gate's clauses hold (`DAGGate.eval_tseitin`,
`values_getD_gate`), and the output clause is the output.''', '''(`values_getD_input`), the gate clauses hold
(`BoolCircuit.DAGCircuit.eval_tseitinGates_values`), and the output clause is the output.''',
            1, "Tseitin sketch")
    log("  toCNF_extension_iff: the gate clauses of the (⇐) direction cite "
        "`DAGCircuit.eval_tseitinGates_values` (P1+, with D4)")
    t = sub(t, '''is serialized as `1^(v+1) 0 b` (`Std.Sat.CNF.serializeLit`), so `numVars ≤ |serialize φ|`.
(Proved, from the serialization's shape.) -/''', '''is serialized as `1^(v+1) 0 b` (`Std.Sat.CNF.serializeLit`), so `numVars ≤ |serialize φ|`.

**Proof sketch.** `numVars` is a right fold of `max` over the literals of `φ` (each variable
plus one), so it suffices to bound each term (`foldr_max_le`). A literal `(v, b)` of a clause
`C` serializes to `v + 3` letters, which lie inside the serialization of `C`, itself inside
that of `φ` (`length_le_length_flatMap`, twice). -/''', 1, "Tseitin numVars sketch")
    log("  numVars_le_length_serialize: proof sketch (leftover of round-1 finding 11)")
    # D4 extended (user, 2026-10-14): the copy of the uniqueness lemma goes
    t = dels(t, ["values_getD_eq_of_eval_tseitinGates"], log, "Tseitin")
    t = sub(t, "      values_getD_eq_of_eval_tseitinGates C hC τ hgates _ C.output_lt]\n",
            "      DAGCircuit.values_getD_eq_of_eval_tseitinGates C hC τ hgates _ C.output_lt]\n", 1,
            "Tseitin re-point")
    t = sub(t, """(⇒) By
`values_getD_eq_of_eval_tseitinGates` the satisfying assignment carries the circuit's values
on its own inputs, which are `σ`'s; the output clause makes the output `1`. -/""", """(⇒) By
`BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates` the satisfying assignment carries
the circuit's values on its own inputs, which are `σ`'s; the output clause makes the output
`1`. -/""", 1, "Tseitin sketch 2")
    t = sub(t, """**Duplication disclosure.** The backward direction re-proves the private
`BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates` of
`TCSlib.Complexity.CircuitComplexity.DAGCircuitSat` (a strong induction over the vertices,
from the public `BoolCircuit.eval_tseitinGates` and `BoolCircuit.DAGGate.eval_tseitin`),
since only the existential closure `satisfiable_iff_toCNF_satisfiable` is public there;
promoting the private lemma would delete this copy.
""", """Both directions cite `TCSlib.Complexity.CircuitComplexity.DAGCircuitSat`: the circuit's values
satisfy the gate clauses (`BoolCircuit.DAGCircuit.eval_tseitinGates_values`), and an assignment
satisfying them carries the circuit's values
(`BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates`).
""", 1, "Tseitin disclosure")
    log("  delete values_getD_eq_of_eval_tseitinGates (L024, D4 extended); toCNF_extension_iff's (⇒) "
        "cites `DAGCircuit.values_getD_eq_of_eval_tseitinGates`; the disclosure replaced by the "
        "citations")
    return t


# ============================================================================ D6, and the core bounds

def e_TQBF(t, log):
    start = "/-! ### Fill appendix: membership validation and the assignment walk -/\n"
    assert t.count(start) == 1
    a = t.index(start)
    d0, s0, e0, ls = lib.locate(t, "b4mFuel_sufficient", TMP)
    b = sum(len(l) + 1 for l in ls[:e0 + 1])
    assert t[b] == "\n", repr(t[b:b + 20])
    seg = t[a:b + 1]
    ds, _ = lib.scan_text(seg, TMP)
    assert len(ds) == 45 and all(d["private"] and d["name"].startswith("b4m") for d in ds), \
        [(d["name"], d["private"]) for d in ds if not (d["private"] and d["name"].startswith("b4m"))]
    lines = seg.count("\n")
    first = t[:a].count("\n") + 1
    t = t[:a] + t[b + 1:]
    log(f"  D6: delete the b4m appendix, base lines {first}-{first + lines - 1} ({lines} lines with"
        f" the following blank line; 45 private declarations, all named b4m*)")
    t = dels(t, ["codec_core_window"], log, "TQBF")
    t = sub(t, "coreCode_inj s (codec_core_window hc) (codec_core_window hd)",
            "coreCode_inj s hc.core_bounds hd.core_bounds", 1, "TQBF core bounds")
    log("  codecRowOf_eq_iff: the window's core-code bounds -> `Turing.Cfg.InWindow.core_bounds` "
        "(the private copy codec_core_window deleted)")
    return t


# ============================================================================ length_lbStep

PBL_HELPER = '''/-- **Dropping leading letters of the components keeps a pair state within `max |s| 2`**:
re-pairing the two components of `s` with `i` and `j` leading letters dropped gives a word no
longer than `s`, or than the empty pair (length `2`) when `s` is not a pair. It is the length
bound of the pair-stepping block loops (`xorPairStep` here, the level-bit loop of the `TQBF`
reduction).

**Proof sketch.** If `s` decodes as `⟨a, b⟩`, the new pair is no longer than `s`
(`length_pairEncode`); otherwise both components are empty and the new pair is the empty
pair. -/
theorem length_pairEncode_drop_le (s : List Bool) (i j : ℕ) :
    (pairEncode ((pairFstD s).drop i) ((pairSndD s).drop j)).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode, List.length_drop]
    omega
'''


def e_PolyTimeBlockLoop(t, log):
    d0, s0, e0, ls = lib.locate(t, "length_pair_components_le", TMP)
    t = "\n".join(ls[:e0 + 1] + [""] + PBL_HELPER.rstrip("\n").split("\n") + ls[e0 + 1:])
    log(f"  insert length_pairEncode_drop_le after length_pair_components_le (base line {s0 + 1})")
    t = sub(t, '''/-- One XOR round never grows the state beyond `max` with the empty pair. -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [xorPairStep, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega
''', '''/-- One XOR round never grows the state beyond `max` with the empty pair
(`length_pairEncode_drop_le` with one letter dropped from each component). -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 :=
  length_pairEncode_drop_le s 1 1
''', 1, "PBL length_xorPairStep_le")
    log("  length_xorPairStep_le: the instance `length_pairEncode_drop_le s 1 1`")
    return t


def e_TQBFHardParams(t, log):
    t = sub(t, '''/-- The round does not lengthen a state beyond `max |s| 2`. -/
private theorem length_lbStep (s : List Bool) : (lbStep s).length ≤ max s.length 2 := by
  cases hd : pairDecode s with
  | none =>
    have hf : pairFstD s = [] := by simp [pairFstD, hd]
    have hs : pairSndD s = [] := by simp [pairSndD, hd]
    simp [lbStep, hf, hs, length_pairEncode]
  | some uv =>
    obtain ⟨u, v⟩ := uv
    have he := eq_pairEncode_of_pairDecode s u v hd
    subst he
    simp only [lbStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega
''', '''/-- The round does not lengthen a state beyond `max |s| 2` (the shared pair-step bound
`Complexity.length_pairEncode_drop_le`, dropping one letter of the countdown only). -/
private theorem length_lbStep (s : List Bool) : (lbStep s).length ≤ max s.length 2 :=
  length_pairEncode_drop_le s 0 1
''', 1, "Params length_lbStep")
    log("  length_lbStep: the instance `length_pairEncode_drop_le s 0 1`")
    return t


# ============================================================================ G-prefix

def e_TQBFHardSemantics(t, log):
    t = dels(t, ["prefixTruth_congr_agree"], log, "Semantics")
    log("  (G-prefix: moved to `Formulas/QBF` as `Complexity.QBF.prefixTruth_congr_agree`; its 2 "
        "uses resolve to it through `open QBF`)")
    return t


def e_QBF(t, base_semantics, log):
    moved = lib.decl_text(base_semantics, "prefixTruth_congr_agree", TMP)
    t = sub(t, '''/-- Prefix truth depends on its leaf predicate only through its truth values. (Proved, by
induction on the prefix.) -/
theorem prefixTruth_congr {P P' : (ℕ → Bool) → Prop} (h : ∀ τ, P τ ↔ P' τ)
    (qs : List Quant) (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P qs σ i ↔ PrefixTruth P' qs σ i := by
  induction qs generalizing σ i with
  | nil => exact h σ
  | cons q qs ih =>
    cases q with
    | ex => exact exists_congr fun b => ih _ _
    | all => exact forall_congr' fun b => ih _ _
''', moved + '''

/-- Prefix truth depends on its leaf predicate only through its truth values. (Proved: the case
of `prefixTruth_congr_agree` with leaves that agree everywhere.) -/
theorem prefixTruth_congr {P P' : (ℕ → Bool) → Prop} (h : ∀ τ, P τ ↔ P' τ)
    (qs : List Quant) (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P qs σ i ↔ PrefixTruth P' qs σ i :=
  prefixTruth_congr_agree qs σ i fun τ _ => h τ
''', 1, "QBF congr")
    log("  insert prefixTruth_congr_agree (TQBFHardSemantics' text, verbatim) before "
        "prefixTruth_congr; prefixTruth_congr its corollary (G-prefix)")
    t = sub(t, "## Main results\n\n", "## Main results\n\n"
            "* `Complexity.QBF.prefixTruth_congr_agree` — prefix truth from `(σ, i)` sees the leaf "
            "only on\n  assignments that agree with `σ` below `i`.\n", 1, "QBF doc")
    return t


# ============================================================================ leftovers (comments)

def e_TQBFHardMachine(t, log):
    t = sub(t, '''along the code-level step relation `Complexity.Codec.StepRel`. (Proved, by induction along
the path.) -/''', '''along the code-level step relation `Complexity.Codec.StepRel`.

**Proof sketch.** Induction along the path. The empty path stays at the word of `u`, and
binary words are injective (`bits_injective`). A last step into the word of `c` is a step
pair `⟨x, ⟨γ, ⟨bits c, bits s⟩⟩⟩` of the step language; its nested pairs decode
(`pairEncode_inj`) to `γ = bits c₁` for a code `c₁` reached by induction, so the last step
is `StepRel N x s c₁ c`. -/''', 1, "Machine sketch")
    log("  reflTransGen_stepRel: proof sketch (leftover of round-1 finding 11)")
    return t


def e_TQBFHardVerifier(t, log):
    t = sub(t, '''component is an assignment of the prefix variables, it is the flat matrix (`predB_iff`).
''', '''component is an assignment of the prefix variables, it is the flat matrix
(`Complexity.TQBFHard.predB_iff`, in `TQBFHardBridge`).
''', 1, "Verifier prose")
    t = sub(t, "* `Complexity.TQBFHard.predB_iff` — on an assignment it is the flat matrix.\n", "", 1,
            "Verifier results")
    log("  module docstring: the Main results entry for predB_iff (declared in TQBFHardBridge) "
        "removed; the prose names its home")
    return t


def e_ExpBFSRun(t, log):
    t = sub(t, '''/-- **The chain to the next iteration**: `s` is incremented and `U`, `V`, `w`, `K`, `Bs`, `c`,
`c1`, `s1` are cleared. -/''', '''/-- **The chain to the next iteration**: `s` is incremented and `U`, `V`, `w`, `K`, `Bs`, `c`,
`c1`, `s1` are cleared.

**Proof sketch.** Nine straight-line steps: the increment of `s` (`inc_step`, within the bound
`s + 1 ≤ B`) and eight clears (`clr_step`), each keeping the register bounds; the run ends at
the first label of the radius copy. -/''', 1, "Run nz_run sketch")
    log("  nz_run: proof sketch (leftover of round-1 finding 11)")
    return t


def e_SpaceComplexity(t, log):
    t = sub(t, '''  growing radii; the breadth-first search memory machine; `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))`
  for `S ≥ logSpace`
''', '''  growing radii; the breadth-first search memory machine;
  `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))` for `S ≥ logSpace`
''', 1, "facade line 1")
    t = sub(t, '''  file and deciders of its query register machine, the machine and its runs; every `NL` language logspace-reduces to `PATH` (Thm 4.18, consumed by
  `PATH_NLComplete` in `SpaceComplexity.Logspace.Path`)
''', '''  file and deciders of its query register machine, the machine and its runs; every `NL`
  language logspace-reduces to `PATH` (Thm 4.18, consumed by `PATH_NLComplete` in
  `SpaceComplexity.Logspace.Path`)
''', 1, "facade line 2")
    log("  the two Contents lines over 100 columns re-wrapped (leftover of round-1 finding 11)")
    return t


reg("DAGCircuitSat", C + "CircuitComplexity/DAGCircuitSat.lean", "code")
reg("TQBFHardTseitin", C + "ClassPSPACE/TQBFHardTseitin.lean", "code")
reg("TQBF", C + "ClassPSPACE/TQBF.lean", "code")
reg("PolyTimeBlockLoop", C + "ClassNP/PolyTimeBlockLoop.lean", "code")
reg("TQBFHardParams", C + "ClassPSPACE/TQBFHardParams.lean", "code")
reg("TQBFHardSemantics", C + "ClassPSPACE/TQBFHardSemantics.lean", "code")
reg("QBF", C + "Formulas/QBF.lean", "code")
reg("TQBFHardMachine", C + "ClassPSPACE/TQBFHardMachine.lean", "comment")
reg("TQBFHardVerifier", C + "ClassPSPACE/TQBFHardVerifier.lean", "comment")
reg("ExpBFSRun", SC + "ExpBFS/Run.lean", "comment")
reg("SpaceComplexity", C + "SpaceComplexity.lean", "comment")

DELTAS["DAGCircuitSat"] = {"imports": [], "groups": [
    ("namespace BoolCircuit\n\nopen Std.Sat (CNF)\n\nnamespace DAGCircuit\n\nvariable {n : ℕ}\n\n",
     ["eval_tseitinGates_values", "values_getD_eq_of_eval_tseitinGates"],
     "end DAGCircuit\n\nend BoolCircuit\n")]}
DELTAS["PolyTimeBlockLoop"] = {"imports": [], "groups": [
    ("namespace Complexity\n\nopen Turing\n\n", ["length_pairEncode_drop_le"], "end Complexity\n")]}
DELTAS["QBF"] = {"imports": [], "groups": [
    ("namespace Complexity\n\nopen Std.Sat (CNF)\n\nnamespace QBF\n\n", ["prefixTruth_congr_agree"],
     "end QBF\n\nend Complexity\n")]}
# edit functions that read another base file (QBF receives TQBFHardSemantics' lemma)
EXTRA_INPUT = {"QBF": "TQBFHardSemantics"}

# The SpaceComplexity facade (comments only) is elaborated as its own text: a cut inlining
# its 38 D1-affected modules cannot elaborate, for the base text as for the landed one (the
# union of their imports makes `Complexity.LogProg.Mem` of `Machines/MARM` visible in
# `ISCountGenWalk`, whose own closure lacks it; probes.py's control FacadeFull shows it).
# Its D1-affected imports are covered by the consumer cuts below.
OWN_TEXT_ONLY = {"SpaceComplexity"}
# Consumer cuts (not landed modules): the maximal modules downstream of a restated module that
# no changed module's cut covers, and the ClassPSPACE facade. They elaborate the D1 consumers.
CONSUMERS = ["TCSlib.Complexity.SpaceComplexity.ExpTime",
             "TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi",
             "TCSlib.Complexity.SpaceComplexity.Savitch",
             "TCSlib.Complexity.ClassPSPACE"]

# ============================================================================ freeze metadata
# Full names. A statement change is authorized only as D1's mechanical rewrite (freeze.py
# checks `after == rewrite(before)`); a body change either as that rewrite or by BODY.
NDTM, FIN, CDC = "Turing.NDTM.", "Turing.FinNDTM.", "Complexity.Codec."
LP = "Complexity.LogProg."
D1_FILES = set(RESTATED) | {"ConfigGraph"}
PROMOTED = {
    "ConfigGraph": {NDTM + n for n in CG_PROMOTE},
    "InputAccess": {LP + "access_width_half"},
    "DAGCircuitSat": {"BoolCircuit.DAGCircuit.eval_tseitinGates_values",
                      "BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates"},
}
ADDED = {
    "ConfigGraph": {"Turing.Cfg.InWindow.core_bounds", FIN + "DecidesInSpace.mem_of_acceptsWithin",
                    "Turing.outSummary_eq_empty_iff"},
    "InputAccess": {LP + "arm_chain", LP + "boundedDecodeStride_loop", LP + "drop_canon",
                    "Complexity.indicator_inputBitLang", "Complexity.indicator_inputLenLang",
                    "Complexity.pairEncode_getD_snd"},
    "PolyTimeBlockLoop": {"Complexity.length_pairEncode_drop_le"},
    "QBF": {"Complexity.QBF.prefixTruth_congr_agree"},
}
B4M = None  # filled by freeze.py from the base (the 45 b4m* declarations, asserted)
DELETED = {
    "ConfigGraph": {("Turing.InWindow", "D1: the private window predicate"),
                    ("Turing.inWindow_iff_cfgInWindow", "D1: its bridge")}
    | {(("Complexity." if n in CG_S1B[6:] else FIN) + n, "dead s1b block") for n in CG_S1B},
    "Word": {(CDC + "InWin", "D1: copy of the window predicate")},
    "Checks": {(CDC + "outSummary_eq_empty_iff",
                "G-outsum: moved to ConfigGraph as Turing.outSummary_eq_empty_iff")},
    "Bridge": {(CDC + "take_succ_action", "D2h copy"), (CDC + "abs_lt_card_visitedWith", "D2h copy"),
               (CDC + "mem_visitedWith_of_ne_none", "D2h copy"),
               (CDC + "visitedWith_take_subset", "D2h copy"),
               (CDC + "inWin_runWith_take", "D2 copy"), (CDC + "mem_of_acceptsWithin", "D3 copy")},
    "Radius": {("Complexity.ExpBFS.inWin_of_coreSum_eq", "D5 copy")},
    "QueryReshape": {("Complexity.drop_canon",
                      "G-canon: moved to InputAccess as Complexity.LogProg.drop_canon")},
    "TQBF": {("Complexity.codec_core_window",
              "private copy of the core bounds; Turing.Cfg.InWindow.core_bounds")},
    "TQBFHardTseitin": {("Complexity.TQBFHard.values_getD_eq_of_eval_tseitinGates",
                         "D4 copy (D4 extended by the user, 2026-10-14)")},
    "TQBFHardSemantics": {("Complexity.TQBFHard.prefixTruth_congr_agree",
                           "G-prefix: moved to Formulas/QBF as Complexity.QBF.prefixTruth_congr_agree")},
}
# deletions that are moves: landed name -> deleted (file, name); statement and body must agree
MOVES = {"Turing.outSummary_eq_empty_iff": ("Checks", CDC + "outSummary_eq_empty_iff"),
         LP + "drop_canon": ("QueryReshape", "Complexity.drop_canon"),
         "Complexity.QBF.prefixTruth_congr_agree":
             ("TQBFHardSemantics", "Complexity.TQBFHard.prefixTruth_congr_agree")}
BODY = {
    "ConfigGraph": {FIN + "DecidesInSpace.mem_iff_acceptsWithin_configBound",
                    FIN + "count_windowed_vertices",
                    NDTM + "runWith_take_inWindow", NDTM + "inWindow_of_coreSum_eq"},
    "Word": {CDC + "coreSum_eq_of_cfgWord_eq"},
    "Valid": {CDC + "cellOf_mkCfg", CDC + "vScan_cfgWord"},
    "Step": {CDC + "boundary_iff", CDC + "cellOf_apply"},
    "Checks": {CDC + "initChk_iff"},
    "Bridge": {CDC + "mem_iff_codeChain", CDC + "mem_of_codePath"},
    "Radius": {"Complexity.ExpBFS." + n for n in (
        "inWin_init", "inWin_mono", "inWin_runWith_of_decides", "inWin_stepWith", "rcode_iff",
        "winRun_of_card_eq")},
    "InputAccess": {LP + "arm_increments", LP + "boundedDecode_loop"},
    "Engine": {CDC + n for n in ("decChain", "decodeStride_loop", "halvCount_loop", "incChain")},
    "QueryReshape": {"Complexity.drop_bit", "Complexity.drop_len", "Complexity.comp_suffix_address"},
    "Mult": {"Complexity.mult_addresses"},
    "Run": {CDC + "orc_bit", CDC + "orc_len"},
    "TQBFARMMachine": {LP + "TQBFARM.orc_bit", LP + "TQBFARM.orc_len"},
    "Parse": {CDC + "canon_of_getLastD", CDC + "getLastD_of_canon", CDC + "pe_getD_snd"},
    "VWord": {"Complexity.getD_drop"},
    "TQBFHardTseitin": {"Complexity.TQBFHard.toCNF_extension_iff"},
    "TQBF": {"Complexity.codecRowOf_eq_iff"},
    "PolyTimeBlockLoop": {"Complexity.length_xorPairStep_le"},
    "TQBFHardParams": {"Complexity.TQBFHard.length_lbStep"},
    "QBF": {"Complexity.QBF.prefixTruth_congr"},
}
DOC = {
    "ConfigGraph": {FIN + "DecidesInSpace.mem_iff_acceptsWithin_configBound",
                    NDTM + "inWindow_of_coreSum_eq"},
    "Bridge": {CDC + "mem_iff_codeChain", CDC + "mem_of_codePath"},
    "Radius": {"Complexity.ExpBFS.inWin_runWith_of_decides", "Complexity.ExpBFS.rcode_iff"},
    "InputAccess": {LP + "access_width_half", LP + "arm_increments", LP + "boundedDecode_loop"},
    "Engine": BODY["Engine"],
    "TQBFHardTseitin": {"Complexity.TQBFHard.numVars_le_length_serialize",
                        "Complexity.TQBFHard.toCNF_extension_iff"},
    "PolyTimeBlockLoop": {"Complexity.length_xorPairStep_le"},
    "TQBFHardParams": {"Complexity.TQBFHard.length_lbStep"},
    "QBF": {"Complexity.QBF.prefixTruth_congr"},
    "TQBFHardMachine": {"Complexity.TQBFHard.reflTransGen_stepRel"},
    "ExpBFSRun": {"Complexity.LogProg.ExpBFS.nz_run"},
}
# files whose module docstring or other comments outside declarations change (a whitespace-only
# re-wrap, as in the SpaceComplexity facade, is not a change under the comparison)
MODDOC = {"ConfigGraph", "Word", "Bridge", "InputAccess", "Engine", "VWord", "TQBF", "QBF",
          "TQBFHardVerifier", "TQBFHardTseitin"}
# files whose imports change: key -> imports added
IMPORTS = {"VWord": ["TCSlib.Programs.Util.List"]}
# Hydroxyi's files (copyright "TCSlib contributors", author Hydroxyi): read from the headers

# ============================================================================ width wraps
# Whitespace-only re-wraps of added lines over 100 columns (code points; four of them are D1's
# rewrite lengthening an existing line by four letters). Applied by land.py after each file's
# edits, each asserted once.
WRAPS = {
    "Bridge": [('''the window `[-s, s]` (`Turing.NDTM.runWith_take_inWindow`: compare with a branch of the halting budget —
padding the accepting word, or truncating it where every branch has halted); the codes of
''', '''the window `[-s, s]` (`Turing.NDTM.runWith_take_inWindow`: compare with a branch of the
halting budget — padding the accepting word, or truncating it where every branch has halted);
the codes of
''')],
    "InputAccess": [('''* `Complexity.LogProg.access_width_half`, `Complexity.LogProg.drop_canon` — halving removes one binary
  digit; the tail loop's flag is `Canon`.
''', '''* `Complexity.LogProg.access_width_half`, `Complexity.LogProg.drop_canon` — halving removes one
  binary digit; the tail loop's flag is `Canon`.
''')],
    "Langs": [('''        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧ cfgCode s C' = c' := by
''', '''        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := by
''')],
    "Radius": [('''the run extended by the pair's choice bit, still in the window (`Turing.NDTM.inWindow_of_coreSum_eq`). -/
''', '''the run extended by the pair's choice bit, still in the window
(`Turing.NDTM.inWindow_of_coreSum_eq`). -/
''')],
    "Word": [('''  if h : ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c then some (Classical.choose h)
''', '''  if h : ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c then
    some (Classical.choose h)
'''), ('''  have h : ∃ D : Cfg N.k Bool N.State x, Cfg.InWindow s D ∧ cfgCode s D = cfgCode s C := ⟨C, hC, rfl⟩
''', '''  have h : ∃ D : Cfg N.k Bool N.State x, Cfg.InWindow s D ∧ cfgCode s D = cfgCode s C :=
    ⟨C, hC, rfl⟩
''')],
}
