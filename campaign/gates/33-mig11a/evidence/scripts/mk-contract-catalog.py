"""MIG-11a, Build/Contract/Catalog: R3 copy and the framed compare as contracts, with their field
equations and the copy's frame. Every edit is asserted unique.
Usage: python3 -I mk-contract-catalog.py <worktree root>"""
import sys
root = sys.argv[1]
p = f"{root}/TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean"
s = open(p).read()


def rep(a, b):
    global s
    n = s.count(a)
    assert n == 1, (n, a[:80])
    s = s.replace(a, b)


rep("""/-- The mapped copy frames exactly the destination interval: its footprint is
""", """/-- **R3 copy as a contract** (MIG-11a, user 2026-10-16): the index is the source word `w`.
Started in the sweep phase with `w` delimited at the head of tape `src`, the copy reaches `done`
at exactly `2|w| + 2`, and not earlier, with the destination interval `[pos, pos + |w|)` of tape
`dst` (from its head `pos`) holding `w` cell by cell and every other cell unchanged; the heads of
`src` and `dst` stay within one cell of their intervals and every other head is fixed.

**Proof sketch.** `Turing.sweepContract` with the clauses of `Turing.copyTM_run_ofCfg`. -/
def copyTM_contract (src dst : Fin k) (hne : src ≠ dst) (x : List Γ) :
    Contract (copyTM k src dst) SweepPhase.sweep {some SweepPhase.done} (List Γ) x :=
  sweepContract _ _ _ src (fun j => j = src ∨ j = dst) x
    (sweepPost .done dst fun w d j q => FinTM.bufferTape w (q - d.workTapePos j)) (fun _ _ => rfl)
    (copyTM_run_ofCfg src dst hne)

/-- R3 copy frames exactly the destination interval: its footprint is `[pos, pos + |w|)` on tape
`dst` and empty elsewhere (MIG-11a, user 2026-10-16).

**Proof sketch.** `Turing.sweep_ite_keep` at `dst`. -/
theorem copyTM_contract_frames (src dst : Fin k) (hne : src ≠ dst) (x : List Γ) :
    (copyTM_contract src dst hne x).Frames fun w d j =>
      if j = dst then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ :=
  fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq

/-- The mapped copy frames exactly the destination interval: its footprint is
""")

rep("""/-! ### The specification API (user, 2026-10-16)

The data fields of every contract in this file""", """/-- **The framed compare as a contract** (MIG-11a, user 2026-10-16): the index is the pair of
words `(u, v)`, delimited at the heads of tapes `fst` and `snd`. From the working phase the
compare reaches the verdict `done (decide (u = v))` at exactly `2 · compareStop u v + 2`, with no
verdict earlier and nothing written; the two heads stay within `[pos - 1, pos + compareStop u v]`
and every other head is fixed. The exits are both verdicts, so the exit is not a singleton and
the contract is built directly.

**Proof sketch.** Each field is the matching clause of `Turing.compareTM_run_stop_ofCfg`; the
exit lies in the range at the verdict; a fixed head lies in its one-point interval. -/
def compareTM_contract [DecidableEq Γ] (fst snd : Fin k) (hne : fst ≠ snd) (x : List Γ) :
    Contract (compareTM k fst snd) FlagPhase.run (Set.range fun b => some (FlagPhase.done b))
      (List Γ × List Γ) x where
  pre p d := (∀ q : ℤ, -1 ≤ q → q ≤ (p.1.length : ℤ) →
      d.workTapes fst (d.workTapePos fst + q) = FinTM.bufferTape p.1 q) ∧
    ∀ q : ℤ, -1 ≤ q → q ≤ (p.2.length : ℤ) →
      d.workTapes snd (d.workTapePos snd + q) = FinTM.bufferTape p.2 q
  time p _ := 2 * compareStop p.1 p.2 + 2
  post p d := { d with state := some (FlagPhase.done (decide (p.1 = p.2))) }
  lo p d j := if j = fst ∨ j = snd then d.workTapePos j - 1 else d.workTapePos j
  hi p d j := if j = fst ∨ j = snd then d.workTapePos j + (compareStop p.1 p.2 : ℤ)
    else d.workTapePos j
  run p d hd hp := (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).1
  exit_mem _ _ _ _ := ⟨_, rfl⟩
  cut p d hd hp u hu h := by
    obtain ⟨b, hb⟩ := h
    exact (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).2.1 u hu b hb.symm
  env p d hd hp u hu j := by
    have h := (compareTM_run_stop_ofCfg fst snd hne p.1 p.2 d hd hp.1 hp.2).2.2 j u hu
    split_ifs at h ⊢ with hj
    · exact h
    · rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-! ### The specification API (user, 2026-10-16)

The data fields of every contract in this file""")

rep("""attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  seekEndTM_contract seekStartTM_contract scanTM_contract
""", """attribute [simps! (config := { isSimp := false }) pre time post lo hi]
  seekEndTM_contract seekStartTM_contract scanTM_contract
attribute [simps! (config := { isSimp := false }) pre time post lo hi] copyTM_contract
attribute [simps (config := { isSimp := false }) pre time post lo hi] compareTM_contract
""")

rep("""* `Turing.walkTM_contract`, `Turing.skipTM_contract`, `Turing.skipBackTM_contract`,
  `Turing.seekEndTM_contract`, `Turing.seekStartTM_contract`, `Turing.scanTM_contract`: the
  lockstep walk, the seek family and the scan as contracts (§13d G4), with the seek family's
  endpoint `Turing.seekPost`.
""", """* `Turing.walkTM_contract`, `Turing.skipTM_contract`, `Turing.skipBackTM_contract`,
  `Turing.seekEndTM_contract`, `Turing.seekStartTM_contract`, `Turing.scanTM_contract`: the
  lockstep walk, the seek family and the scan as contracts (§13d G4), with the seek family's
  endpoint `Turing.seekPost`.
* `Turing.copyTM_contract`, `Turing.compareTM_contract`: R3 copy and the framed compare as
  contracts (MIG-11a, user 2026-10-16), with `Turing.copyTM_contract_frames`. The counter rows'
  contracts are in `Build/Contract/Counter`.
""")
open(p, "w").write(s)
print("ok")
