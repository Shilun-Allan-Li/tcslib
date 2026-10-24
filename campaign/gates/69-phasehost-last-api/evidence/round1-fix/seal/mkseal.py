"""Build the sealed copies of the five re-pointed files (python3 -I mkseal.py <worktree> <outdir>)."""
import sys, pathlib, re
wt, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])

SEAL = """section PHLSeal
attribute [local irreducible] Turing.phaseHostTM Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.step Turing.Cfg.mapState Turing.Action.mapState Turing.Action.apply
  Turing.embedEmitTM
attribute [-simp] Turing.Action.apply
-- Controls: each closes unsealed (PHLSealControl.lean) and must fail here.
example {k : ℕ} {Γ I : Type} {Ph : I → Type} (M : (i : I) → Turing.MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) :
    (Turing.phaseHostTM M q0 red).q₀ = q0 := rfl
example {k : ℕ} {S : Type} {x : List Bool} (M : Turing.MultiTapeTM k Bool S)
    (d : Turing.Cfg k Bool S x) : M.runFrom d 0 = d := rfl
example {k : ℕ} {S : Type} {x : List Bool} (M : Turing.MultiTapeTM k Bool S)
    (d : Turing.Cfg k Bool S x) : M.step { d with state := none } = { d with state := none } := rfl
example {k : ℕ} {S T : Type} {x : List Bool} (d : Turing.Cfg k Bool S x) (f : S → T) :
    (d.mapState f).inputPos = d.inputPos := rfl
example {k : ℕ} {S T : Type} (a : Turing.Action k Bool S) (f : S → T) :
    (a.mapState f).output = a.output := rfl
example {k : ℕ} {S : Type} {x : List Bool} (a : Turing.Action k Bool S)
    (d : Turing.Cfg k Bool S x) : (a.apply d).state = a.state := rfl
example {m k : ℕ} {S : Type} (ι : Fin m ↪ Fin k) (M : Turing.MultiTapeTM m Bool S) :
    (Turing.embedEmitTM ι M).q₀ = M.q₀ := rfl
"""

def decl_text(t, head):
    """The declaration starting at the line `head` up to the next blank line followed by `/--`."""
    i = t.index(head)
    j = t.index("\n\n/--", i)
    return t[i:j + 1]

def build(path, anchor, body, name):
    t = (wt / path).read_text()
    assert t.count(anchor) == 1, (path, anchor)
    sec = SEAL + body + "end PHLSeal\n\n"
    (out / name).write_text(t.replace(anchor, sec + anchor))
    print("built", name)

WR = "TCSlib/Complexity/TuringMachine/Build/WindowRun.lean"
t = (wt / WR).read_text()
wr = decl_text(t, "private theorem wr_prefix {k")
assert wr.count("wr_prefix") == 1
build(WR, "/-- At a timeout the runner makes exactly one stationary dispatch to exhaustion. -/",
      wr.replace("wr_prefix", "wr_prefix'"), "WindowRunSeal.lean")

SB = "TCSlib/Complexity/TuringMachine/Build/StepBlock.lean"
t = (wt / SB).read_text()
sb = decl_text(t, "private lemma recordSkipTM_tail {k")
assert sb.count("recordSkipTM_tail") == 1
build(SB, "/-- A trusted action record splits at exactly the inherited fixed width.",
      sb.replace("recordSkipTM_tail", "recordSkipTM_tail'"), "StepBlockSeal.lean")

IN = "TCSlib/Complexity/SpaceComplexity/Inclusions.lean"
inc = """-- `b2b_trial_run`'s `hpz`, the test host's last (verdict) phase.
example (MV MI MP : FinTM Bool) {x : List Bool}
    (z : Cfg (b2b_tapeCount MV.k MI.k MP.k) Bool (b2b_testState MV MI .verdict) x) (t : ℕ) :
    (b2b_testTM MV MI MP).runFrom (z.mapState (Sigma.mk B2bTestPhase.verdict)) t =
      ((b2b_testPhases MV MI MP .verdict).runFrom z t).mapState
        (Sigma.mk B2bTestPhase.verdict) :=
  phaseHostTM_run_le (b2b_testPhases MV MI MP) ⟨.anchor, ()⟩ (b2b_testRedirect MV MI)
    .verdict z t (fun _ _ _ _ => rfl) t le_rfl
-- `b2b_round_run`'s `hprefix`, with the start written as the tagged `c`.
example (MV MI MP : FinTM Bool) {x : List Bool}
    (c : Cfg (b2b_tapeCount MV.k MI.k MP.k) Bool (Σ j, b2b_testState MV MI j) x) (T : ℕ)
    (hguard : ∀ t < T, ∀ q : Σ j, b2b_testState MV MI j,
      ((b2b_testTM MV MI MP).runFrom c t).state = some q →
        b2b_bodyRedirect MV MI .test q = none)
    (t : ℕ) (htt : t ≤ T) :
    (b2b_bodyTM MV MI MP).runFrom (c.mapState (Sigma.mk B2bBodyPhase.test)) t =
      ((b2b_testTM MV MI MP).runFrom c t).mapState (Sigma.mk B2bBodyPhase.test) :=
  phaseHostTM_run_le (b2b_bodyPhases MV MI MP) ⟨.test, ⟨.anchor, ()⟩⟩
    (b2b_bodyRedirect MV MI) .test c T hguard t htt
-- `b2b_finish_answer`'s `hp`, the host's answer phase.
example (MV MI MP : FinTM Bool) {x : List Bool} (b : Bool)
    (c : Cfg (b2b_tapeCount MV.k MI.k MP.k + 1) Bool (Fin 2) x) (t : ℕ) :
    (b2b_host MV MI MP).tm.runFrom
        (c.mapState (Sigma.mk (β := b2b_hostState MV MI MP) (B2bHostPhase.answer b))) t =
      ((b2b_answerTM (b2b_tapeCount MV.k MI.k MP.k + 1) b).runFrom c t).mapState
        (Sigma.mk (β := b2b_hostState MV MI MP) (B2bHostPhase.answer b)) :=
  phaseHostTM_run_le (b2b_hostPhases MV MI MP) _ (b2b_hostRedirect MV MI MP)
    (.answer b) c t (fun _ _ _ _ => rfl) t le_rfl
"""
build(IN, "/-- After counter exhaustion the host reuses the shared trial and emits its", inc,
      "InclusionsSeal.lean")

CS = "TCSlib/Complexity/TuringMachine/CodeSimulator.lean"
cs = """-- `canonEmitVerdict`'s `leaf`, with the proof's own phase family and redirects.
example {k : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM k Bool S) (entry : S) (exit : Option Bool → S) {x : List Bool}
    (z : Cfg k Bool Bool x) : True := by
  classical
  let Ph : Bool → Type
    | false => S
    | true => Bool
  let family (b : Bool) : MultiTapeTM k Bool (Ph b) := match b with
    | false => M
    | true => canonHaltTM k
  let start : Sigma Ph := ⟨false, entry⟩
  let red (b : Bool) : Ph b → Option (Sigma Ph) := match b with
    | true => fun _ => none
    | false => fun q =>
      if q = exit (some true) then some ⟨true, true⟩
      else if q = exit none ∨ q = exit (some false) then some ⟨true, false⟩ else none
  let N := phaseHostTM family start red
  have leaf : N.runFrom (z.mapState (Sigma.mk true)) 1 =
      ((canonHaltTM k).runFrom z 1).mapState (Sigma.mk true) :=
    phaseHostTM_run_le family start red true z 1 (fun _ _ _ _ => rfl) 1 le_rfl
  trivial
"""
build(CS, "/-- A Boolean-exit computation becomes a first-return-or-escape round.", cs,
      "CodeSimulatorSeal.lean")

OS = "TCSlib/Complexity/TuringMachine/Build/OracleSim.lean"
os_ = """-- `oracleHost_offQuery`'s table agreement off the query state.
example (M : FinOracleTM Bool) (C : FinTM Bool) (hc : 0 < C.k) (en ex : C.State) :
    ∀ qb : M.State × Bool, qb.1 ≠ M.tm.qQuery → ∀ inp work,
      (oracleHost M C hc en ex).tm.tr
          ((⟨Sigma.mk (β := oraclePhaseState M C) OraclePhase.source, sigma_mk_injective⟩ :
            (M.State × Bool) ↪ Σ i, oraclePhaseState M C i) qb) inp work =
        ((embedEmitTM (oracleSourceBank M.k C.k) (oracleShadowTM (OracleTM.queryTapeIdx M.k)
          M.tm.plainEmptyOracle)).tr qb inp work).mapState
          (⟨Sigma.mk (β := oraclePhaseState M C) OraclePhase.source, sigma_mk_injective⟩ :
            (M.State × Bool) ↪ Σ i, oraclePhaseState M C i) := by
  intro qb hq inp work
  exact phaseHostTM_tr_of_red_none (oraclePhases M C hc en) _ (oracleRedirect M C ex)
    .source qb (by simp [oracleRedirect, hq]) inp work
"""
build(OS, "/-- A local administration segment and its one redirect step inside the full", os_,
      "OracleSimSeal.lean")
