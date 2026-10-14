"""The asserted edits of the B6 hosts landing, beyond the placed parts (read by gate.py).

Each entry is (old, new); gate.py asserts that `old` occurs exactly once in the file after the
parts are placed, then replaces it. Paths are relative to the worktree root.
"""

TM = "TCSlib/Complexity/TuringMachine/"
SC = "TCSlib/Complexity/SpaceComplexity/"

EDITS = {}

# StateRenaming: the module docstring lists the two new results.
EDITS[TM + "StateRenaming.lean"] = [
    ("""* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond
  at every time.
""",
     """* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond
  at every time.
* `Turing.MultiTapeTM.relabelState_visitedByTapeHead`,
  `Turing.MultiTapeTM.relabelState_spaceUsed` — so do head trajectories and space at
  every time (the space clause of the coding step).
"""),
]

# Encoding: the module docstring lists the new results; `exists_codeTM` becomes the time clause
# of `exists_codeTM_spaceUsed` (statement unchanged), so that the relabelling is built once.
EDITS[TM + "Encoding.lean"] = [
    ("""* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).
""",
     """* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).
* `Turing.exists_codeTM_spaceUsed` — the same coded machine also uses the same space at
  every time; `Turing.CodeTM.one_le_spaceUsed` — every coded run visits a cell.
"""),
    ("""The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
""",
     """The implementation is the time clause of `Turing.exists_codeTM_spaceUsed`, whose witness
is this relabelling (`Turing.MultiTapeTM.relabelState`, from the shared state-renaming module
`TCSlib.Complexity.TuringMachine.StateRenaming`), so that the relabelling is built once. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  obtain ⟨M', h, -⟩ := exists_codeTM_spaceUsed M hk
  exact ⟨M', h⟩
"""),
]

# ConfigCount: the module docstring lists the new results.
EDITS[SC + "ConfigCount.lean"] = [
    ("""  [AB09, §4.1.1, the deterministic case of Thm 4.2]
* `Complexity.LOGSPACE_subset_P`""",
     """  [AB09, §4.1.1, the deterministic case of Thm 4.2]
* `Turing.FinTM.ComputesInTime.spaceUsed_le_of_halt`,
  `Turing.FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` — the halt-time
  space bound holds at every time, in the form the space-preserving normal form needs.
* `Turing.FinTM.decidesInSpace_of_alphabetReduction` — a rich-alphabet machine deciding on the
  `Bool` inputs within an all-input space bound gives a `SPACE` decider. [AB09, Claim 1.5]
* `Complexity.LOGSPACE_subset_P`"""),
]

# CfgRecord: the module docstring lists the new lemma.
EDITS[TM + "Build/CfgRecord.lean"] = [
    ("""* `Turing.cfgRecord_length` — a record has `k + 3` fields.
""",
     """* `Turing.cfgRecord_length` — a record has `k + 3` fields.
* `Turing.Cfg.inWindow_init` — the initial configuration is in every window.
"""),
]

# ConfigGraph: the module docstring lists the public code; S1b's private copies are deleted
# and their uses re-pointed at the public declarations (user decision B3, 2026-10-13).
EDITS[SC + "ConfigGraph.lean"] = [
    ("""* `Turing.OutSummary`, `Turing.outSummary` — the three-valued output summary.
""",
     """* `Turing.OutSummary`, `Turing.outSummary` — the three-valued output summary.
* `Turing.outSummaryCode`, `Turing.summaryTag` — its `Fin 3` code and the tag update on
  codes: the record tag of the windowed runner H3 (`SpaceComplexity/WindowClock.lean`), and
  the summary code of the vertex records below.
"""),
    ("""* `Turing.outSummary_append_congr` — a common output suffix preserves summary equality.
""",
     """* `Turing.outSummary_append_congr` — a common output suffix preserves summary equality.
* `Turing.summaryTag_append`, `Turing.outSummaryCode_eq_one_iff` — the tag update tracks
  appending, and the code `1` is exactly the output `[true]`.
"""),
    ("""/-- Encode the three output summaries without adding a finiteness instance. -/
private def sumCode : OutSummary → Fin 3
  | .empty => 0
  | .accept => 1
  | .dead => 2

/-- Distinct summaries have distinct three-element codes. -/
private theorem sumCode_injective : Function.Injective sumCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [sumCode]

""", ""),
    ("""  let code j := (MultiTapeTM.ConfigCount.coreCode s (cs j), sumCode (outSummary (cs j).output))
""",
     """  let code j :=
    (MultiTapeTM.ConfigCount.coreCode s (cs j), outSummaryCode (outSummary (cs j).output))
"""),
    ("""    · exact sumCode_injective (congrArg Prod.snd eqcode)
""",
     """    · exact outSummaryCode_injective (congrArg Prod.snd eqcode)
"""),
    ("""/-- The canonical rich record of a graph vertex, using S1a's summary code.
""",
     """/-- The canonical rich record of a graph vertex, using the summary code `Turing.outSummaryCode`.
"""),
    ("""  cfgRecord s c (sumCode (outSummary c.output))
""",
     """  cfgRecord s c (outSummaryCode (outSummary c.output))
"""),
    ("""and the tag. S1a's injective `sumCode` recovers the output summary. -/
""",
     """and the tag. The injective `Turing.outSummaryCode` recovers the output summary. -/
"""),
    ("""    sumCode_injective.eq_iff]
""",
     """    outSummaryCode_injective.eq_iff]
"""),
    ("""/-- Representatives of the three summary codes, used only to compute tag
updates. The encoding itself is the received `sumCode`. -/
private def s1b_summaryWord (τ : Fin 3) : List Bool :=
  if τ = sumCode .empty then [] else if τ = sumCode .accept then [true] else [false]

/-- Each chosen representative has the requested summary code.

**Proof sketch.** Check the three elements of `Fin 3`; the existing encoding
computes on the empty, accepting and dead representative words. -/
private theorem s1b_summaryWord_code (τ : Fin 3) :
    sumCode (outSummary (s1b_summaryWord τ)) = τ := by
  fin_cases τ <;> rfl

/-- The record-step tag update is summary append on a representative word. -/
private def s1b_tagUpdate (τ : Fin 3) (b : Option Bool) : Fin 3 :=
  sumCode (outSummary (s1b_summaryWord τ ++ b.toList))

/-- An absent emission preserves the tag, as required by `recordStepTM`.

**Proof sketch.** Appending no symbol preserves the representative word. -/
private theorem s1b_tagUpdate_none (τ : Fin 3) : s1b_tagUpdate τ none = τ := by
  simpa [s1b_tagUpdate] using s1b_summaryWord_code τ

/-- The finite tag update agrees with every actual output history.

**Proof sketch.** The representative and actual word have equal summaries
by injectivity of S1a's code. Apply its append-congruence theorem. -/
private theorem s1b_tagUpdate_output (u : List Bool) (b : Option Bool) :
    s1b_tagUpdate (sumCode (outSummary u)) b = sumCode (outSummary (u ++ b.toList)) := by
  exact congrArg sumCode (outSummary_append_congr
    (sumCode_injective (s1b_summaryWord_code (sumCode (outSummary u)))) b.toList)

""", ""),
    ("""`accept`, by S1a's injective code; its summary accepts precisely `[true]`. -/
""",
     """`accept`, by the injective `Turing.outSummaryCode`; its summary accepts precisely `[true]`. -/
"""),
    ("""    (c.state = none ∧ sumCode (outSummary c.output) = sumCode .accept) ↔
""",
     """    (c.state = none ∧ outSummaryCode (outSummary c.output) = outSummaryCode .accept) ↔
"""),
    ("""  rw [sumCode_injective.eq_iff, outSummary_eq_accept_iff]
""",
     """  rw [outSummaryCode_injective.eq_iff, outSummary_eq_accept_iff]
"""),
]

# Hierarchy: the module docstring and one sentence of `space_hierarchy`'s docstring change with
# the strengthened `space_universal` (placed as part K); `space_hierarchy`'s statement and the
# two corollaries are untouched.
EDITS[SC + "Hierarchy.lean"] = [
    ("""convention — `AroraBarakChapters3-4Plan.md` §2.4). Phase P4.3; on 2026-10-12
`space_universal` was restated forward-only and `space_hierarchy`'s sketch
moved to the window route (`machine-library-design.md` §16b item 3,
`backlog.md` RD-3), both pending their statement gate.
""",
     """convention — `AroraBarakChapters3-4Plan.md` §2.4). Phase P4.3; on 2026-10-12
`space_universal` was restated forward-only and `space_hierarchy`'s sketch
moved to the window route (`machine-library-design.md` §16b item 3,
`backlog.md` RD-3; statement gate passed 2026-10-13), and on 2026-10-13
`space_universal` was strengthened to the addend-free `C · s`, pending the
statement gate of its hosts (H3, H5 and `U₀`).
"""),
    ("""  the machine tests no budget, runs no clock and replays nothing. Its space
  bound carries a `+ logSpace n` addend for its input device (the simulated
  input is a suffix of its input, read through a binary position) — a
  declared deviation from Exercise 4.1's literal `C_α · t`, which presumes the
  standing `S(n) > log n` convention.
""",
     """  the machine tests no budget, runs no clock and replays nothing. Its space
  bound is Exercise 4.1's `C_α · t`, with no addend: the simulated input, a
  suffix of its input, is read through H5's bounded-prefix ruler device
  (`Turing.exists_rulerHostTM`), a unary ruler of the header's length, which
  the bound absorbs because every qualifying run visits a cell (strengthened
  2026-10-13 from a `+ logSpace n` addend).
"""),
    ("""* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12).
""",
     """* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12; addend-free `C · s` since 2026-10-13).
"""),
    ("""[AB09]; spec, fill pending — phase P4.3, sketch moved to the window route
2026-10-12 by design §16b item 3, statement gate pending): for
""",
     """[AB09]; spec, fill pending — phase P4.3, sketch moved to the window route
2026-10-12 by design §16b item 3, RD-3 statement gate passed 2026-10-13): for
"""),
    ("""same output, having visited at most `C_α · (s + 1)` cells. This is
`space_universal`'s forward clause with the native device in place of the
binary-position one, hence without its logarithmic addend; only this
direction is used.
""",
     """same output, having visited at most `C_α · (s + 1)` cells
(`Turing.exists_selfUniversal`). This is `space_universal`'s forward clause
with the native device in place of the bounded-prefix ruler, so no header
ruler is needed; only this direction is used.
"""),
]

# The facades import the four new modules and list them.
EDITS["TCSlib/Complexity/TuringMachine.lean"] = [
    ("""import TCSlib.Complexity.TuringMachine.Build.Contract
""",
     """import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.TuringMachine.Build.InputDevice
"""),
    ("""import TCSlib.Complexity.TuringMachine.UniversalStartup
""",
     """import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.SelfUniversal
"""),
    ("""  `ReturnContract.release` as thin wrappers over the public rows. Proved; MIG-0a gate closed.
""",
     """  `ReturnContract.release` as thin wrappers over the public rows. Proved; MIG-0a gate closed.
* `Build/StepClock`, `Build/WindowRun` — host H3 (`machine-library-design.md` §14): the
  step-clocked runner, shared with the nondeterministic time hierarchy; the semantic windowed
  run `windowRun`; the windowed round loop and the step-clocked windowed runner. Statement gate
  pending; the specification is proved, the machine contracts are sorried.
* `Build/InputDevice` — host H5: the input-device interface, the native device, and the
  bounded-prefix ruler device with its host transformer. Statement gate pending.
"""),
    ("""  total-function form, and the time-bounded variant (code-first input layout).
""",
     """  total-function form, and the time-bounded variant (code-first input layout).
* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Statement gate pending.
"""),
]

EDITS["TCSlib/Complexity/SpaceComplexity.lean"] = [
    ("""import TCSlib.Complexity.SpaceComplexity.ConfigGraph
""",
     """import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.WindowClock
"""),
    ("""- `SpaceComplexity.ConfigGraph`: configuration graphs, the ND Claim 4.4(1), Thm 4.2(iii),
  `NL ⊆ P`, Ex 4.3 (chapters-3-4 campaign, phase P4.2)
""",
     """- `SpaceComplexity.ConfigGraph`: configuration graphs, the ND Claim 4.4(1), Thm 4.2(iii),
  `NL ⊆ P`, Ex 4.3 (chapters-3-4 campaign, phase P4.2)
- `SpaceComplexity.WindowClock`: the windowed runner (host H3) under a configuration-count
  clock, window containment, and the windowed run of a halting space-bounded computation
  (the space hierarchy's window route; statement gate pending)
"""),
]
