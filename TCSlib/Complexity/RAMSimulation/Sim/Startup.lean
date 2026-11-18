/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
import TCSlib.Complexity.RAMSimulation.WordSize

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

attribute [local irreducible] Turing.Contract.ofReaches

/-!
# Stage 2's simulation: the start-up

Before the first instruction, the simulating machine computes the word size `W = W (|x|)` with
the word-size witness, prepares its eight tapes and installs the start memory: the cell `-1`
holds `|x|` modulo `2^W` and every other cell `0` (`WordRAM.initMem`). This file constructs that
start-up for any word-size witness `Mw`; its extra tapes hold `Mw`'s tapes, and its output, which
is captured on a work tape.

## Main results

* `WordRAM.Sim.exists_startup`: the start-up reaches a configuration encoding
  `XCfg.init W |x|` within `tw + O(|x| + W² + 1)` steps and `sw + O(W + log |x| + 1)` cells,
  where `Mw` writes `Nat.bits W` within `tw` steps and `sw` cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §4.1, space-constructible functions.)
-/

namespace WordRAM.Sim

open Turing

/-! ## Private facts about the initial memory -/

/-- The marked startup entry stores the length word at the distinguished cell. -/
private theorem startup_initMem_neg_one (W n : ℕ) : initMem W n (-1) = wd W n := by
  rw [initMem_def, Function.update_self]

/-- Every other startup cell holds zero. -/
private theorem startup_initMem_of_ne (W n : ℕ) (z : ℤ) (hz : z ≠ -1) :
    initMem W n z = 0 := by
  rw [initMem_def, Function.update_of_ne hz]

/-- The singleton table is the initial memory as soon as the distinguished cell's signed
range obligation is supplied. This isolates that obligation from the tape construction.

**Proof sketch.** Use `tableOf_iff`. The singleton has distinct keys and its entry is the key
of `-1`, with the word given by `initMem_def`. For completeness, a nonzero cell must equal
`-1`, since `initMem_def` makes every other cell zero. -/
private theorem startup_tableOf (a W n : ℕ) (hr : InRange (W + a) (-1)) :
    TableOf a W {-1} (initMem W n) [(keyBits a W (-1), bvBits (wd W n))] := by
  rw [tableOf_iff]
  refine ⟨by simp only [List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_self], ?_, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst e
    refine ⟨-1, Finset.mem_singleton_self _, hr, ?_⟩
    rw [startup_initMem_neg_one]
  · intro z _ hz
    have he : z = -1 := by
      by_contra hne
      exact hz (startup_initMem_of_ne W n z hne)
    subst z
    simp only [List.map_cons, List.map_nil, List.mem_singleton]

/-- Every positive width represents `-1`, including the single-bit boundary. -/
private theorem startup_inRange_neg_one (k : ℕ) (hk : 1 ≤ k) : InRange k (-1) := by
  rw [inRange_iff]
  have hp : (2 : ℤ) ^ 1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hp ⊢
  constructor <;> omega

/-- Every width at least two represents `-1` in the signed range. -/
private theorem startup_inRange_neg_one_of_two_le (k : ℕ) (hk : 2 ≤ k) : InRange k (-1) := by
  exact startup_inRange_neg_one k (by omega)

/-- The finished eight tapes encode the initial RAM configuration once the distinguished
address's range fact is supplied.

**Proof sketch.** Read the encoding with `encodes_iff` and initialization with `XCfg.init_def`.
The table clause is `startup_tableOf`; the register, length, scratch and origin clauses are the
hypotheses. The initial output is empty in either output mode. -/
private theorem startup_encodes_of_tapes {K : ℕ} {S : Type} {x : List Bool} {W : ℕ}
    (a : ℕ) (fn : Bool) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ) (d : Turing.Cfg K Bool S x)
    (hr : InRange (W + a) (-1))
    (hheads : ∀ j : Fin 8, d.workTapePos (σ j) = o j)
    (htable : KeyTableAt d (σ 0) (o 0)
      [(keyBits a W (-1), bvBits (wd W x.length))])
    (hkey : ∃ w, WordAt d (σ 1) w ∧ w.length = W + a)
    (hregs : ∀ r : Fin 8, 2 ≤ r.val → r.val ≤ 4 → ∃ w, WordAt d (σ r) w ∧ w.length = W)
    (hlen : WordAt d (σ 5) (Nat.bits x.length))
    (hblank : ∀ r : Fin 8, 6 ≤ r.val → ∀ q : ℤ, d.workTapes (σ r) q = none)
    (hout : d.output = []) : Encodes a fn {-1} (XCfg.init W x.length) σ o d := by
  rw [encodes_iff, XCfg.init_def]
  refine ⟨hheads, ⟨_, htable, startup_tableOf a W x.length hr⟩, hkey, hregs, hlen, hblank, ?_⟩
  cases fn <;> simpa only [Bool.false_eq_true, if_false, if_true] using hout

/-! ## Private word and capture facts -/

/-- The length word consists of the low input-length bits, padded by false bits to its width. -/
private theorem startup_lengthWord (W n : ℕ) :
    bvBits (wd W n) = List.ofFn (fun j : Fin W => (Nat.bits n).getD j.val false) := by
  change bvBits (BitVec.ofInt W (n : ℤ)) = _
  rw [BitVec.ofInt_natCast, bvBits_def]
  apply congrArg (fun f : Fin W → Bool => List.ofFn f)
  funext j
  rw [BitVec.getLsbD_ofNat]
  simp only [j.isLt, decide_true, Bool.true_and]
  rw [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

/-- The shared returning silent embedding captures the width witness at its first live exit.

**Proof sketch.** Read the bounded computation with `FinTM.computesInTime_iff`, invoke
`embedSilentRetTM_firstReturn`, and identify the fresh start with `embedSilentCfg_initCfg`.
The capture and unselected-frame field readers give the binary width, its ending head,
the empty physical output and every untouched tape. -/
private theorem startup_capture {K : ℕ} (Mw : FinTM Bool) (σ : Fin Mw.k ↪ Fin K)
    (cap : Fin K) (hcap : cap ∉ Set.range σ) (x : List Bool) (W tw : ℕ)
    (hMw : Mw.ComputesInTime x (Nat.bits W) tw) :
    ∃ t ≤ tw,
      (∀ s < t, ((embedSilentRetTM σ cap Mw.tm).runFrom
        (Turing.Cfg.init (Sum.inl Mw.tm.q₀) x) s).state ≠ some (Sum.inr ())) ∧
      let d := (embedSilentRetTM σ cap Mw.tm).runFrom
        (Turing.Cfg.init (Sum.inl Mw.tm.q₀) x) t
      d.state = some (Sum.inr ()) ∧ d.workTapes cap = FinTM.bufferTape (Nat.bits W) ∧
        d.workTapePos cap = ((Nat.bits W).length : ℤ) ∧ d.output = [] ∧
        ∀ j, j ∉ Set.range σ → j ≠ cap →
          d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0 := by
  obtain ⟨halt, out⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hMw
  obtain ⟨t, ht, run, cut⟩ := embedSilentRetTM_firstReturn Mw x σ cap hcap
    (fun _ _ => none) (fun _ => 0) [] tw halt
  rw [embedSilentCfg_initCfg Mw.tm σ cap hcap x] at run cut
  refine ⟨t, ht, cut, ?_⟩
  dsimp only
  rw [run]
  obtain ⟨word, head⟩ := embedSilentCfg_cap σ cap hcap (fun _ _ => none) (fun _ => 0)
    [] [] (Mw.tm.runFrom (Mw.tm.initCfg x) tw)
  rw [List.nil_append, out] at word head
  refine ⟨rfl, word, head, ?_, ?_⟩
  · rw [embedSilentCfg_output]
  · intro j hj hne
    exact embedSilentCfg_unselected σ cap (fun _ _ => none) (fun _ => 0)
      [] [] (Mw.tm.runFrom (Mw.tm.initCfg x) tw) j hj hne

/-- Place the width witness after the eight simulation tapes, before the auxiliary bank. -/
private def startupBank (m r : ℕ) : Fin m ↪ Fin (8 + (m + (r + 1))) :=
  (Fin.castAddEmb (r + 1)).trans (Fin.natAddEmb 8)

/-- The capture tape is the first tape of the final auxiliary bank. -/
private def startupCaptureIndex (m r : ℕ) : Fin (8 + (m + (r + 1))) :=
  Fin.natAdd 8 (Fin.natAdd m (0 : Fin (r + 1)))

/-- The auxiliary capture tape is disjoint from the width witness's bank. -/
private theorem startupCapture_separated (m r : ℕ) :
    startupCaptureIndex m r ∉ Set.range (startupBank m r) := by
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val hj
  change 8 + j.val = 8 + (m + 0) at h
  have hj := j.isLt
  omega

/-- Silent capture adds only the frame/capture tapes' space, with coefficient one on the
width witness's original space.

**Proof sketch.** Rewrite returning visited sets with
`embedSilentRetTM_visitedByTapeHead`. On the selected bank they equal the source visited sets;
off it, the frame uses one cell and the capture uses at most the final output length plus one.
Split the actual tape sum twice with `Fin.sum_univ_add`, separating the first eight tapes,
the source bank, and the final auxiliary bank. The source sum is counted exactly once; bound
each remaining tape by the binary width's length plus one. -/
private theorem startup_capture_space (Mw : FinTM Bool) (r : ℕ) (x : List Bool) (W tw : ℕ)
    (hMw : Mw.ComputesInTime x (Nat.bits W) tw) :
    (embedSilentRetTM (startupBank Mw.k r) (startupCaptureIndex Mw.k r) Mw.tm).spaceUsed
      (Turing.Cfg.init (Sum.inl Mw.tm.q₀) x) tw ≤
      Mw.tm.spaceUsed (Mw.tm.initCfg x) tw + (8 + (r + 1)) * ((Nat.bits W).length + 1) := by
  classical
  let σ := startupBank Mw.k r
  let cap := startupCaptureIndex Mw.k r
  have hcap : cap ∉ Set.range σ := startupCapture_separated _ _
  let R := embedSilentRetTM σ cap Mw.tm
  let f := fun j => R.spaceUsedByTape (Turing.Cfg.init (Sum.inl Mw.tm.q₀) x) tw j
  have fresh := embedSilentCfg_initCfg Mw.tm σ cap hcap x
  have out := ((FinTM.computesInTime_iff _ _ _ _).mp hMw).2
  have selected (j : Fin Mw.k) : f (σ j) = Mw.tm.spaceUsedByTape (Mw.tm.initCfg x) tw j := by
    simp only [f, R]
    rw [← fresh, MultiTapeTM.spaceUsedByTape_eq_card, embedSilentRetTM_visitedByTapeHead,
      (embedSilentTM_visitedByTapeHead σ cap hcap Mw.tm (fun _ _ => none)
        (fun _ => 0) [] [] (Mw.tm.initCfg x) tw j).1,
      ← MultiTapeTM.spaceUsedByTape_eq_card]
  have frame (j) (hj : j ∉ Set.range σ) : f j ≤ (Nat.bits W).length + 1 := by
    simp only [f, R]
    rw [← fresh, MultiTapeTM.spaceUsedByTape_eq_card, embedSilentRetTM_visitedByTapeHead,
      ← MultiTapeTM.spaceUsedByTape_eq_card]
    by_cases he : j = cap
    · subst j
      have h := embedSilentTM_spaceUsedByTape_cap σ cap hcap Mw.tm (fun _ _ => none)
        (fun _ => 0) [] [] (Mw.tm.initCfg x) tw
      have hi : (Mw.tm.initCfg x).output = [] := by rw [MultiTapeTM.initCfg_eq, Cfg.init_output]
      rw [out, hi] at h
      simpa only [List.length_nil, Nat.sub_zero] using h
    · rw [(embedSilentTM_visitedByTapeHead_frame σ cap hcap Mw.tm (fun _ _ => none)
        (fun _ => 0) [] [] (Mw.tm.initCfg x) tw j hj he).2]
      omega
  have first : (∑ j : Fin 8, f (Fin.castAdd (Mw.k + (r + 1)) j)) ≤
      8 * ((Nat.bits W).length + 1) := by
    calc
      _ ≤ ∑ _j : Fin 8, ((Nat.bits W).length + 1) := by
        apply Finset.sum_le_sum
        intro j _
        apply frame
        rintro ⟨a, ha⟩
        have he := congrArg Fin.val ha
        change 8 + a.val = j.val at he
        have hj := j.isLt
        omega
      _ = _ := by simp
  have last : (∑ j : Fin (r + 1), f (Fin.natAdd 8 (Fin.natAdd Mw.k j))) ≤
      (r + 1) * ((Nat.bits W).length + 1) := by
    calc
      _ ≤ ∑ _j : Fin (r + 1), ((Nat.bits W).length + 1) := by
        apply Finset.sum_le_sum
        intro j _
        apply frame
        rintro ⟨a, ha⟩
        have he := congrArg Fin.val ha
        change 8 + a.val = 8 + (Mw.k + j.val) at he
        have ha := a.isLt
        omega
      _ = _ := by simp
  have middle : (∑ j : Fin Mw.k, f (Fin.natAdd 8 (Fin.castAdd (r + 1) j))) =
      Mw.tm.spaceUsed (Mw.tm.initCfg x) tw := by
    rw [MultiTapeTM.spaceUsed_eq_sum]
    exact Finset.sum_congr rfl (fun j _ => selected j)
  rw [MultiTapeTM.spaceUsed_eq_sum]
  change (∑ j : Fin (8 + (Mw.k + (r + 1))), f j) ≤ _
  rw [Fin.sum_univ_add, Fin.sum_univ_add
    (fun j : Fin (Mw.k + (r + 1)) => f (Fin.natAdd 8 j)), middle, Nat.add_mul]
  omega

/-! ## Private expansion row -/

/-- The catalog expansion writes a zero register on tape zero and exhausts the binary
counter on tape one, returning only the counter head. -/
private def startupExpandPost {x : List Bool} {S : Type} (exit : S) (W : ℕ)
    (d : Turing.Cfg 2 Bool S x) : Turing.Cfg 2 Bool S x :=
  { d with
    state := some exit
    workTapes := Function.update
      (Function.update d.workTapes 0
        (wordPatch (d.workTapes 0) (d.workTapePos 0) (List.replicate W false))) 1
      (fun q => if d.workTapePos 1 ≤ q ∧
          q < d.workTapePos 1 + ((Nat.bits W).length : ℤ) then some true else d.workTapes 1 q)
    workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (W : ℤ)) }

/-- The existing counter-driven expansion supplies the zero-register writer at every width.

**Proof sketch.** Apply `expandTM_run_ofCfg` to `counterLoopBody 0 d` and the binary width on
the last tape. `counterLoopCfg_body` identifies its start. For the endpoint, compare the body
with the body of `startupExpandPost` through the published body-field readers and
`wordPatch_apply`; the same reconstruction theorem then identifies the entire host endpoint.
The catalog's cut excludes both loop exits, hence the desired `done` exit. -/
private theorem startup_expand_run {x : List Bool} (W : ℕ)
    (d : Turing.Cfg 2 Bool (CounterLoopState (Fin 2)) x)
    (hd : d.state = some (.dec .run)) (hw : WordAt d 1 (Nat.bits W)) :
    (expandTM 1 0 [false]).runFrom d (2 * W + counterOverhead (Nat.bits W) (W + 1)) =
      startupExpandPost .done W d ∧
    (∀ t < 2 * W + counterOverhead (Nat.bits W) (W + 1),
      ((expandTM 1 0 [false]).runFrom d t).state ≠ some .done) := by
  let c := counterLoopBody (0 : Fin 2) d
  let body : Turing.Cfg 1 Bool (Fin 2) x :=
    { c with
      workTapes := fun j q =>
        if j = 0 ∧ c.workTapePos j ≤ q ∧ q < c.workTapePos j + (W : ℤ) then
          FinTM.bufferTape (List.replicate W false) (q - c.workTapePos j)
        else c.workTapes j q
      workTapePos := Function.update c.workTapePos 0 (c.workTapePos 0 + (W : ℤ)) }
  have zero_cast : (0 : Fin 1).castSucc = (0 : Fin 2) := rfl
  have hb : body = counterLoopBody (0 : Fin 2) (startupExpandPost .done W d) := by
    apply Turing.Cfg.ext
    · simp only [body, c, counterLoopBody_state]
    · simp only [body, c, startupExpandPost, counterLoopBody_inputPos]
    · funext j q
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [body, c, startupExpandPost, counterLoopBody_workTapes,
        counterLoopBody_workTapePos, zero_cast, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), wordPatch_apply, true_and,
        List.length_replicate]
    · funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [body, c, startupExpandPost, counterLoopBody_workTapePos, zero_cast,
        Function.update_self]
      change d.workTapePos 0 + (W : ℤ) =
        Function.update d.workTapePos 0 (d.workTapePos 0 + (W : ℤ)) (0 : Fin 2)
      rw [Function.update_self]
    · simp only [body, c, startupExpandPost, counterLoopBody_output]
  have hw' : ∀ q : ℤ, -1 ≤ q → q ≤ ((Nat.bits W).length : ℤ) →
      d.workTapes 1 (d.workTapePos 1 + q) = FinTM.bufferTape (Nat.bits W) q :=
    (wordAt_iff _ _ _).mp hw
  have value : Nat.ofDigits 2 ((Nat.bits W).map Bool.toNat) = W :=
    (counterValue_eq _).symm.trans (counterValue_bits W)
  obtain ⟨run, cut, -, -⟩ := expandTM_run_ofCfg (0 : Fin 1) [false] c
    (by rw [counterLoopBody_state]) (Nat.bits W) (d.workTapes 1) (d.workTapePos 1) hw' W value
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one,
    List.flatten_replicate_singleton, show (1 : ℕ) + 1 = 2 from rfl,
    Nat.mul_comm W 2] at run cut
  have start : counterLoopCfg (some (.dec .run)) c (d.workTapes 1) (d.workTapePos 1) = d := by
    rw [← hd]
    exact counterLoopCfg_body (0 : Fin 2) d
  rw [start] at run cut
  have finish : counterLoopCfg (some .done) body
      (fun q => if d.workTapePos 1 ≤ q ∧ q < d.workTapePos 1 + ((Nat.bits W).length : ℤ)
        then some true else d.workTapes 1 q) (d.workTapePos 1) = startupExpandPost .done W d := by
    rw [hb]
    exact counterLoopCfg_body (0 : Fin 2) (startupExpandPost .done W d)
  refine ⟨?_, fun t ht => (cut t ht).1⟩
  simpa only [body, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Fin.val_zero, c,
    mul_comm 2 W] using run.trans finish

/-- Amortized counter overhead makes the zero-register expansion linear in the width. -/
private theorem startup_expand_time (W : ℕ) :
    2 * W + counterOverhead (Nat.bits W) (W + 1) ≤ 8 * W + 2 := by
  have h := counterOverhead_le (Nat.bits W)
  rw [(counterValue_eq _).symm.trans (counterValue_bits W)] at h
  have hlen := length_bits_le_self W
  omega

/-! ## Private composition of startup stages -/

/-- Erase only a configuration's finite control tag. -/
private def startupErase {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool Unit x := d.mapState (fun _ => ())

/-- Normalize erasure to physical fields before forming arithmetic-dependent conditionals. -/
private theorem startupErase_eq {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) : startupErase d =
      ⟨d.state.map (fun _ => ()), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [startupErase, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output]

/-- Attach a phase's tag to unit-tagged physical data. -/
private def startupAttach {K : ℕ} {S : Type} {x : List Bool} (s : S)
    (d : Turing.Cfg K Bool Unit x) : Turing.Cfg K Bool S x := d.mapState (fun _ => s)

/-- Erasing is invariant under a control relabeling. -/
private theorem startupErase_mapState {K : ℕ} {S T : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (f : S → T) : startupErase (d.mapState f) = startupErase d := by
  simp only [startupErase, Cfg.mapState_mapState]

/-- Re-tagging physical data and then erasing the tag gives the same unit-tagged data. -/
private theorem startupErase_attach {K : ℕ} {S : Type} {x : List Bool} (s : S)
    (d : Turing.Cfg K Bool Unit x) : startupErase (startupAttach s d) = d := by
  rw [startupErase, startupAttach, Cfg.mapState_mapState]
  apply Turing.Cfg.ext
  · rw [Cfg.mapState_state]
    cases h : d.state with
    | none => rfl
    | some u => cases u; rfl
  · rw [Cfg.mapState_inputPos]
  · funext j q; rw [Cfg.mapState_workTapes]
  · funext j; rw [Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output]

/-- A final relabeling may be applied to the phase tag before attachment. -/
private theorem startupAttach_mapState {K : ℕ} {S T : Type} {x : List Bool} (s : S)
    (d : Turing.Cfg K Bool Unit x) (f : S → T) :
    (startupAttach s d).mapState f = startupAttach (f s) d := by
  simp only [startupAttach, Cfg.mapState_mapState]
  rfl

/-- A startup stage is a finite catalog composition together with its physical specification
and time bound. Its heads may move: only the native length stage needs a separate small-space
argument; all subsequent stages get their work envelope from their linear time bound. -/
private structure StartupStage (K : ℕ) (ι : Type) where
  S : Type
  finite : Fintype S
  decEq : DecidableEq S
  M : MultiTapeTM K Bool S
  entry : S
  exit : S
  C : (x : List Bool) → Contract M entry {some exit} ι x
  pre : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Prop
  next : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Turing.Cfg K Bool Unit x
  bound : List Bool → ι → ℕ
  pre_eq : ∀ {x} i (d : Turing.Cfg K Bool S x), (C x).pre i d ↔ pre i (startupErase d)
  post_eq : ∀ {x} i (d : Turing.Cfg K Bool S x),
    (C x).post i d = startupAttach exit (next i (startupErase d))
  time_le : ∀ {x} i (d : Turing.Cfg K Bool S x), d.state = some entry →
    pre i (startupErase d) → (C x).time i d ≤ bound x i

/-- Reindex a catalog contract and strengthen its physical precondition to make a startup
stage. All runtime behavior and envelopes remain the catalog contract's.

**Proof sketch.** Reindex the original contract and strengthen only its precondition. Use
that implication for its run, exit, cut and envelope fields. The supplied forecast equality
and time bound give the stage metadata. -/
private noncomputable def StartupStage.ofContract {K : ℕ} {ι κ S : Type}
    [Fintype S] [DecidableEq S] {M : MultiTapeTM K Bool S} {entry exit : S}
    (C : (x : List Bool) → Contract M entry {some exit} κ x) (index : List Bool → ι → κ)
    (P : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Prop)
    (F : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Turing.Cfg K Bool Unit x)
    (B : List Bool → ι → ℕ)
    (hP : ∀ {x} i (d : Turing.Cfg K Bool S x), d.state = some entry →
      P i (startupErase d) → (C x).pre (index x i) d)
    (hF : ∀ {x} i (d : Turing.Cfg K Bool S x),
      (C x).post (index x i) d = startupAttach exit (F i (startupErase d)))
    (hB : ∀ {x} i (d : Turing.Cfg K Bool S x), d.state = some entry →
      P i (startupErase d) → (C x).time (index x i) d ≤ B x i) : StartupStage K ι where
  S := S
  finite := inferInstance
  decEq := inferInstance
  M := M
  entry := entry
  exit := exit
  C x := {
    pre := fun i d => P i (startupErase d)
    time := fun i d => (C x).time (index x i) d
    post := fun i d => (C x).post (index x i) d
    lo := fun i d => (C x).lo (index x i) d
    hi := fun i d => (C x).hi (index x i) d
    run := fun i d hd hp => (C x).run (index x i) d hd (hP i d hd hp)
    exit_mem := fun i d hd hp => (C x).exit_mem (index x i) d hd (hP i d hd hp)
    cut := fun i d hd hp => (C x).cut (index x i) d hd (hP i d hd hp)
    env := fun i d hd hp => (C x).env (index x i) d hd (hP i d hd hp) }
  pre := P
  next := F
  bound := B
  pre_eq := fun _ _ => Iff.rfl
  post_eq := hF
  time_le := hB

/-- Package a bounded row through `Contract.ofReaches` before composing it as a stage.

**Proof sketch.** Keep the supplied time and radius bounds separate in `Contract.ofReaches`.
Its published precondition, endpoint and chosen-time bound supply the stage specification
through `StartupStage.ofContract`. -/
private noncomputable def StartupStage.ofRow {K : ℕ} {ι S : Type}
    [Fintype S] [DecidableEq S] (M : MultiTapeTM K Bool S) (entry exit : S)
    (P : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Prop)
    (F : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Turing.Cfg K Bool Unit x)
    (B E : List Bool → ι → ℕ)
    (hr : ∀ {x} i (d : Turing.Cfg K Bool S x), d.state = some entry →
      P i (startupErase d) → ReachesWithin M d {some exit} (B x i) (E x i)
        (startupAttach exit (F i (startupErase d))))
    (hx : ∀ {x} i (d : Turing.Cfg K Bool S x), d.state = some entry →
      P i (startupErase d) → (startupAttach exit (F i (startupErase d))).state = some exit) :
    StartupStage K ι :=
  StartupStage.ofContract
    (fun x => Contract.ofReaches (fun i d => P i (startupErase d)) (fun i _ => B x i)
      (fun i _ => E x i) (fun i d => startupAttach exit (F i (startupErase d)))
      (fun i d hd hp => hr i d hd hp) (fun i d hd hp => hx i d hd hp)) (fun _ i => i) P F B
    (by intro x i d _ hp; simpa only [Contract.ofReaches_pre] using hp)
    (by intro x i d; simp only [Contract.ofReaches_post])
    (by
      intro x i d hd hp
      exact Contract.ofReaches_time_le _ _ _ _ _ _ i d hd hp)

/-- Compose stages through the published seam contract, retaining their physical forecasts.

**Proof sketch.** Use `Contract.seq`. The physical precondition is the first stage's, and its
postcondition erases to the first forecast by `startupErase_attach`; this supplies the second
stage's precondition. The post equation is `Contract.seq_post` with both stage equations and
the relabeling identities. `Contract.seq_time` and the two stage bounds give the time sum. -/
private noncomputable def StartupStage.seq {K : ℕ} {ι κ : Type}
    (R : StartupStage K ι) (T : StartupStage K κ) (link : ι → κ)
    (hlink : ∀ {x} i (d : Turing.Cfg K Bool Unit x), R.pre i d →
      T.pre (link i) (R.next i d)) : StartupStage K ι := by
  letI := R.decEq
  let C (x : List Bool) := (R.C x).seq (T.C x) link (by
    intro i d _ hp
    rw [T.pre_eq, startupErase_mapState, R.post_eq, startupErase_attach]
    exact hlink i _ ((R.pre_eq i d).mp hp))
  let joined (x : List Bool) : Contract (seamCompTM R.M R.exit T.M T.entry)
      (Sum.inl R.entry) {some (Sum.inr T.exit)} ι x :=
    { C x with
      exit_mem := by
        intro i d hd hp
        simpa only [Set.image_singleton, Option.map_some] using (C x).exit_mem i d hd hp
      cut := by
        intro i d hd hp u hu he
        exact (C x).cut i d hd hp u hu (by
          simpa only [Set.image_singleton, Option.map_some] using he) }
  refine {
    S := R.S ⊕ T.S
    finite := by letI := R.finite; letI := T.finite; infer_instance
    decEq := by letI := T.decEq; infer_instance
    M := seamCompTM R.M R.exit T.M T.entry
    entry := Sum.inl R.entry
    exit := Sum.inr T.exit
    C := joined
    pre := R.pre
    next := fun i d => T.next (link i) (R.next i d)
    bound := fun x i => R.bound x i + 1 + T.bound x (link i)
    pre_eq := ?_
    post_eq := ?_
    time_le := ?_ }
  · intro x i d
    simp only [joined, C, Contract.seq_pre, R.pre_eq, startupErase_mapState]
  · intro x i d
    simp only [joined, C, Contract.seq_post, T.post_eq, R.post_eq, startupErase_mapState,
      startupErase_attach, startupAttach_mapState]
  · intro x i d hd hp
    let d₁ := d.mapState (fun _ => R.entry)
    let d₂ := ((R.C x).post i d₁).mapState (fun _ => T.entry)
    have hd₁ : d₁.state = some R.entry := by
      simp only [d₁, Cfg.mapState_state, hd, Option.map_some]
    have hp₁ : R.pre i (startupErase d₁) := by
      simpa only [d₁, startupErase_mapState] using hp
    have hq := Set.mem_singleton_iff.mp ((R.C x).exit_mem i d₁ hd₁ ((R.pre_eq i d₁).mpr hp₁))
    have hd₂ : d₂.state = some T.entry := by
      simp only [d₂, Cfg.mapState_state, hq, Option.map_some]
    have hp₂ : T.pre (link i) (startupErase d₂) := by
      simpa only [d₂, R.post_eq, startupErase_mapState, startupErase_attach] using hlink i _ hp₁
    have h₁ := R.time_le i d₁ hd₁ hp₁
    have h₂ := T.time_le (link i) d₂ hd₂ hp₂
    simpa only [joined, C, Contract.seq_time, d₁, d₂] using
      Nat.add_le_add (Nat.add_le_add_right h₁ 1) h₂

/-- Selection and control erasure commute; both keep the same bank and empty source output. -/
private theorem startupErase_select {m K : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin K) (d : Turing.Cfg K Bool S x) :
    startupErase (d.select σ) = (startupErase d).select σ := by
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [startupErase, Cfg.select_eq, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output]

/-- Relabeling an embedded source is relabeling its host, by the shared reconstruction lemma.

**Proof sketch.** Apply `embedEmitCfg_mapState_eq`. Selected tapes and heads are given by
the selected-bank readers; unselected ones by `embedEmitCfg_unselected`. The state, input
and output equations are the remaining embedding and state-map field readers. -/
private theorem startupEmbed_mapState {m K : ℕ} {S T : Type} {x : List Bool}
    (σ : Fin m ↪ Fin K) (tapes : Fin K → ℤ → Option Bool) (heads : Fin K → ℤ)
    (out : List Bool) (c : Turing.Cfg m Bool S x) (f : S → T) :
    (embedEmitCfg σ tapes heads out c).mapState f =
      embedEmitCfg σ tapes heads out (c.mapState f) := by
  apply embedEmitCfg_mapState_eq σ f tapes heads out c
  · rw [embedEmitCfg_state, Cfg.mapState_state]
  · rw [embedEmitCfg_inputPos, Cfg.mapState_inputPos]
  · rw [embedEmitCfg_output, Cfg.mapState_output]
  · intro j
    rw [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
    constructor
    · funext q; rw [Cfg.mapState_workTapes]
    · rw [Cfg.mapState_workTapePos]
  · intro j hj
    obtain ⟨ht, hp⟩ := embedEmitCfg_unselected σ tapes heads out (c.mapState f) j hj
    exact ⟨ht.symm, hp.symm⟩

/-- Place a stage in any selected tape bank using `Contract.embed`.

**Proof sketch.** The contract is exactly the public embedding. Its precondition and time
are read on the selection. Erasure commutes with selection by `startupErase_select`, and the
embedded endpoint commutes with attachment by `startupEmbed_mapState`. The ambient frame's
tape, head and output fields are unchanged by erasure, by the published state-map readers. -/
private noncomputable def StartupStage.embed {m K : ℕ} {ι : Type}
    (σ : Fin m ↪ Fin K) (T : StartupStage m ι) : StartupStage K ι where
  S := T.S
  finite := T.finite
  decEq := T.decEq
  M := embedEmitTM σ T.M
  entry := T.entry
  exit := T.exit
  C x := Contract.embed σ (T.C x)
  pre i d := T.pre i (d.select σ)
  next i d := embedEmitCfg σ d.workTapes d.workTapePos d.output (T.next i (d.select σ))
  bound := T.bound
  pre_eq i d := by rw [Contract.embed_pre, T.pre_eq, startupErase_select]
  post_eq i d := by
    rw [Contract.embed_post, T.post_eq, startupErase_select]
    simp only [startupAttach]
    rw [← startupEmbed_mapState]
    have ht : (startupErase d).workTapes = d.workTapes := by
      funext j q; rw [startupErase, Cfg.mapState_workTapes]
    have hp : (startupErase d).workTapePos = d.workTapePos := by
      funext j; rw [startupErase, Cfg.mapState_workTapePos]
    have ho : (startupErase d).output = d.output := by rw [startupErase, Cfg.mapState_output]
    rw [ht, hp, ho]
  time_le i d hd hP := by
    rw [Contract.embed_time]
    apply T.time_le i (d.select σ)
    · simpa only [Cfg.select_eq] using hd
    · simpa only [startupErase_select] using hP

/-- A uniform work radius for the chosen contract time of a startup stage. -/
private def StartupStage.Radius {K : ℕ} {ι : Type} (T : StartupStage K ι)
    (E : List Bool → ι → ℕ) : Prop :=
  ∀ {x} i (d : Turing.Cfg K Bool T.S x), d.state = some T.entry →
    T.pre i (startupErase d) → ∀ u ≤ (T.C x).time i d, ∀ j,
      |(T.M.runFrom d u).workTapePos j - d.workTapePos j| ≤ (E x i : ℤ)

/-- Every stage's time bound is also a sufficient work radius. -/
private theorem StartupStage.radius_time {K : ℕ} {ι : Type} (T : StartupStage K ι) :
    T.Radius T.bound := by
  intro x i d hd hp u hu j
  have h := (T.C x).time_envelope i d u hu j
  rw [Finset.mem_Icc] at h
  have hb : ((T.C x).time i d : ℤ) ≤ T.bound x i := by
    exact_mod_cast T.time_le i d hd hp
  rw [abs_le]
  constructor <;> omega

/-- Read a symmetric contract envelope as a stage radius. -/
private theorem StartupStage.radius_of_box {K : ℕ} {ι : Type} (T : StartupStage K ι)
    (E : List Bool → ι → ℕ)
    (hlo : ∀ {x} i (d : Turing.Cfg K Bool T.S x) j,
      (T.C x).lo i d j = d.workTapePos j - E x i)
    (hhi : ∀ {x} i (d : Turing.Cfg K Bool T.S x) j,
      (T.C x).hi i d j = d.workTapePos j + E x i) : T.Radius E := by
  intro x i d hd hp u hu j
  have h := (T.C x).env i d hd ((T.pre_eq i d).mpr hp) u hu j
  rw [hlo, hhi, Finset.mem_Icc] at h
  rw [abs_le]
  constructor <;> omega

/-- A selected-bank embedding preserves a source radius, since every other head is fixed.

**Proof sketch.** Use the public embedding run equation and its reconstruction of the
selected start. On a selected tape the host head is the source head; on an unselected tape
it is the initial frame head. The embedded contract time is the source time. -/
private theorem StartupStage.radius_embed {m K : ℕ} {ι : Type} (σ : Fin m ↪ Fin K)
    (T : StartupStage m ι) (E : List Bool → ι → ℕ) (hE : T.Radius E) :
    (T.embed σ).Radius E := by
  intro x i d hd hp u hu j
  have ht : u ≤ (T.C x).time i (d.select σ) := by
    simpa only [StartupStage.embed, Contract.embed_time] using hu
  have hs : (d.select σ).state = some T.entry := by simpa only [Cfg.select_eq] using hd
  have hP : T.pre i (startupErase (d.select σ)) := by
    simpa only [StartupStage.embed, startupErase_select] using hp
  have run := embedEmitTM_runFrom σ T.M d.workTapes d.workTapePos d.output (d.select σ) u
  rw [embedEmitCfg_select σ d] at run
  change |((embedEmitTM σ T.M).runFrom d u).workTapePos j - d.workTapePos j| ≤ _
  rw [run]
  by_cases hj : j ∈ Set.range σ
  · obtain ⟨a, rfl⟩ := hj
    rw [embedEmitCfg_selected_pos]
    simpa only [Cfg.select_eq] using hE i (d.select σ) hs hP u ht a
  · rw [(embedEmitCfg_unselected σ d.workTapes d.workTapePos d.output
      (T.M.runFrom (d.select σ) u) j hj).2]
    simp only [sub_self, abs_zero, Nat.cast_nonneg]

/-- Sequential stages add their radii; the dispatch is stationary.

**Proof sketch.** Apply the public joint-trajectory composition to the two radius
relations. During the first stage use its radius directly. During the second, use its
radius around the first endpoint and the first radius at that endpoint; the triangle
inequality gives the sum around the original start. -/
private theorem StartupStage.radius_seq {K : ℕ} {ι κ : Type}
    (R : StartupStage K ι) (T : StartupStage K κ) (link : ι → κ)
    (hlink : ∀ {x} i (d : Turing.Cfg K Bool Unit x), R.pre i d →
      T.pre (link i) (R.next i d))
    (E : List Bool → ι → ℕ) (F : List Bool → κ → ℕ)
    (hR : R.Radius E) (hT : T.Radius F) :
    (R.seq T link hlink).Radius (fun x i => E x i + F x (link i)) := by
  letI := R.decEq
  intro x i d hd hp u hu j
  let P := fun i (d : Turing.Cfg K Bool R.S x) (p : Fin K → ℤ) =>
    ∀ j, |p j - d.workTapePos j| ≤ (E x i : ℤ)
  let Q := fun i (d : Turing.Cfg K Bool T.S x) (p : Fin K → ℤ) =>
    ∀ j, |p j - d.workTapePos j| ≤ (F x i : ℤ)
  have hr : (R.C x).Traj P := (Contract.traj_iff _ _).mpr
    (fun i d hd hp u hu => hR i d hd ((R.pre_eq i d).mp hp) u hu)
  have ht : (T.C x).Traj Q := (Contract.traj_iff _ _).mpr
    (fun i d hd hp u hu => hT i d hd ((T.pre_eq i d).mp hp) u hu)
  have hjoin := Contract.Traj.seq (hlink := by
    intro i d _ hp
    rw [T.pre_eq, startupErase_mapState, R.post_eq, startupErase_attach]
    exact hlink i _ ((R.pre_eq i d).mp hp)) hr ht
  have trace := (Contract.traj_iff _ _).mp hjoin i d hd
    (by simpa only [StartupStage.seq, Contract.seq_pre, R.pre_eq,
      startupErase_mapState] using hp) u hu
  let d₁ := d.mapState (fun _ => R.entry)
  have hd₁ : d₁.state = some R.entry := by
    simp only [d₁, Cfg.mapState_state, hd, Option.map_some]
  have hp₁ : R.pre i (startupErase d₁) := by
    simpa only [d₁, startupErase_mapState, StartupStage.seq] using hp
  rcases trace with h | h
  · have h' := h j
    simp only [Cfg.mapState_workTapePos] at h'
    change |( (R.seq T link hlink).M.runFrom d u).workTapePos j - d.workTapePos j| ≤
      ((E x i + F x (link i) : ℕ) : ℤ)
    exact h'.trans (by omega)
  · have h' := h j
    have he := hR i d₁ hd₁ hp₁ ((R.C x).time i d₁) le_rfl j
    rw [(R.C x).run i d₁ hd₁ ((R.pre_eq i d₁).mpr hp₁)] at he
    simp only [Cfg.mapState_workTapePos] at h'
    simp only [d₁, Cfg.mapState_workTapePos] at he
    have tri := abs_sub_le (((R.seq T link hlink).M.runFrom d u).workTapePos j)
      (((R.C x).post i d₁).workTapePos j) (d.workTapePos j)
    change |((R.seq T link hlink).M.runFrom d u).workTapePos j - d.workTapePos j| ≤
      ((E x i + F x (link i) : ℕ) : ℤ)
    have hh : |((R.seq T link hlink).M.runFrom d u).workTapePos j -
        ((R.C x).post i d₁).workTapePos j| ≤ (F x (link i) : ℤ) := h'
    simpa only [Nat.cast_add, add_comm] using tri.trans (add_le_add hh he)

/-- Strengthen a stage and replace its forecast by an equal one under that precondition.

**Proof sketch.** Keep the original machine, chosen time, cut and envelope. The stronger
precondition supplies the old one; the old run followed by the forecast equality supplies
the new endpoint. No runtime adapter or extra transition is introduced. -/
private noncomputable def StartupStage.spec {K : ℕ} {ι : Type} (T : StartupStage K ι)
    (P : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Prop)
    (F : {x : List Bool} → ι → Turing.Cfg K Bool Unit x → Turing.Cfg K Bool Unit x)
    (hP : ∀ {x} i (d : Turing.Cfg K Bool Unit x), P i d → T.pre i d)
    (hF : ∀ {x} i (d : Turing.Cfg K Bool Unit x), P i d → T.next i d = F i d) :
    StartupStage K ι where
  S := T.S
  finite := T.finite
  decEq := T.decEq
  M := T.M
  entry := T.entry
  exit := T.exit
  C x := {
    pre := fun i d => P i (startupErase d)
    time := (T.C x).time
    post := fun i d => startupAttach T.exit (F i (startupErase d))
    lo := (T.C x).lo
    hi := (T.C x).hi
    run := by
      intro i d hd hp
      rw [(T.C x).run i d hd ((T.pre_eq i d).mpr (hP i _ hp)), T.post_eq, hF i _ hp]
    exit_mem := by
      intro i d hd hp
      have he := (T.C x).exit_mem i d hd ((T.pre_eq i d).mpr (hP i _ hp))
      rwa [T.post_eq, hF i _ hp] at he
    cut := fun i d hd hp => (T.C x).cut i d hd ((T.pre_eq i d).mpr (hP i _ hp))
    env := fun i d hd hp => (T.C x).env i d hd ((T.pre_eq i d).mpr (hP i _ hp)) }
  pre := P
  next := F
  bound := T.bound
  pre_eq := fun _ _ => Iff.rfl
  post_eq := fun _ _ => rfl
  time_le := fun i d hd hp => T.time_le i d hd (hP i _ hp)

/-- A physical configuration template leaves the native input position as its parameter. -/
private abbrev StartupTemplate (K : ℕ) :=
  {x : List Bool} → ℕ → Fin (x.length + 2) → Turing.Cfg K Bool Unit x

/-- A preparation route records its two physical templates and a linear time coefficient. -/
private structure StartupRoute (K : ℕ) (A B : StartupTemplate K) where
  stage : StartupStage K ℕ
  left_input : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), (A W ip).inputPos = ip
  right_input : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), (B W ip).inputPos = ip
  pre_eq : ∀ {x} W (d : Turing.Cfg K Bool Unit x), stage.pre W d ↔ d = A W d.inputPos
  next_eq : ∀ {x} W (d : Turing.Cfg K Bool Unit x), stage.next W d = B W d.inputPos
  coefficient : ℕ
  bound_le : ∀ x W, stage.bound x W ≤ coefficient * (W + (Nat.bits x.length).length + 1)

/-- Package a catalog stage checked on two explicit physical templates.

**Proof sketch.** Specialize the precondition to equality with the start template. Rewriting
that equality reduces the stage's row to the supplied template calculation. Preserve the
machine and time by `StartupStage.spec`; its new forecast is the end template at the same
native input position. -/
private noncomputable def StartupRoute.ofStage {K : ℕ} (A B : StartupTemplate K)
    (T : StartupStage K ℕ)
    (hA : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), (A W ip).inputPos = ip)
    (hB : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), (B W ip).inputPos = ip)
    (hP : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), T.pre W (A W ip))
    (hF : ∀ {x : List Bool} W (ip : Fin (x.length + 2)), T.next W (A W ip) = B W ip)
    (c : ℕ) (hc : ∀ x W, T.bound x W ≤ c * (W + (Nat.bits x.length).length + 1)) :
    StartupRoute K A B where
  stage := T.spec (fun W d => d = A W d.inputPos) (fun W d => B W d.inputPos)
    (by intro x W d hd; rw [hd]; exact hP W _)
    (by
      intro x W d hd
      change T.next W d = B W d.inputPos
      rw [hd, hA]
      exact hF W _)
  left_input := hA
  right_input := hB
  pre_eq := fun _ _ => Iff.rfl
  next_eq := fun _ _ => rfl
  coefficient := c
  bound_le := hc

/-- Join preparation routes with the shared seam, matching their common physical template.

**Proof sketch.** At the first forecast the native position is unchanged, so the second
template equality is reflexive. Compose the stages and their next-template equations. The
dispatch costs one step, absorbed by the positive factor `W + |bits |x|| + 1`.
-/
private noncomputable def StartupRoute.seq {K : ℕ} {A B D : StartupTemplate K}
    (R : StartupRoute K A B) (T : StartupRoute K B D) : StartupRoute K A D := by
  have link : ∀ {x} W (d : Turing.Cfg K Bool Unit x), R.stage.pre W d →
      T.stage.pre W (R.stage.next W d) := by
    intro x W d _
    rw [T.pre_eq, R.next_eq, R.right_input]
  refine {
    stage := R.stage.seq T.stage id link
    left_input := R.left_input
    right_input := T.right_input
    pre_eq := ?_
    next_eq := ?_
    coefficient := R.coefficient + T.coefficient + 1
    bound_le := ?_ }
  · intro x W d
    exact R.pre_eq W d
  · intro x W d
    change T.stage.next W (R.stage.next W d) = D W d.inputPos
    rw [R.next_eq, T.next_eq, R.right_input]
  · intro x W
    change R.stage.bound x W + 1 + T.stage.bound x W ≤
      (R.coefficient + T.coefficient + 1) * (W + (Nat.bits x.length).length + 1)
    have hR := R.bound_le x W
    have hT := T.bound_le x W
    nlinarith

/-- Normalize a route's final template without changing its machine or time metadata. -/
private def StartupRoute.withTarget {K : ℕ} {A B : StartupTemplate K}
    (R : StartupRoute K A B) (D : StartupTemplate K) (he : @B = @D) : StartupRoute K A D where
  stage := R.stage
  left_input := R.left_input
  right_input := by rw [← he]; exact R.right_input
  pre_eq := R.pre_eq
  next_eq := by rw [← he]; exact R.next_eq
  coefficient := R.coefficient
  bound_le := R.bound_le

/-! ## Private catalog stages -/

/-- The word predicate sees only physical fields, so it is invariant under control erasure. -/
private theorem startup_wordAt_erase {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (j : Fin K) (w : List Bool) :
    WordAt (startupErase d) j w ↔ WordAt d j w := by
  rw [wordAt_iff, wordAt_iff]
  simp only [startupErase, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- The expansion forecast commutes with attaching its specified exit control. -/
private theorem startupExpand_attach {S : Type} {x : List Bool} (exit : S) (W : ℕ)
    (d : Turing.Cfg 2 Bool S x) : startupExpandPost exit W d =
      startupAttach exit (startupExpandPost () W (startupErase d)) := by
  rw [startupErase_eq]
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [startupExpandPost, startupAttach, Cfg.mapState_state,
      Cfg.mapState_inputPos, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Cfg.mapState_output, Option.map_some, Function.update_apply, ite_apply, wordPatch_apply]

/-- The zero-register expansion as a reusable two-tape startup stage.

**Proof sketch.** Package `startup_expand_run` through `StartupStage.ofRow`.
`startup_expand_time` bounds its exact time by `8W + 2`; the universal head-speed interval
then bounds its work radius by the same number. The postcondition is
`startupExpand_attach`, and its unit-tagged forecast has the specified live exit. -/
private noncomputable def startupExpandStage : StartupStage 2 ℕ :=
  StartupStage.ofRow (expandTM 1 0 [false]) (.dec .run) .done
    (fun W d => WordAt d 1 (Nat.bits W)) (fun W d => startupExpandPost () W d)
    (fun _ W => 8 * W + 2) (fun _ W => 8 * W + 2)
    (by
      intro x W d hd hp
      have hr := startup_expand_run W d hd ((startup_wordAt_erase d 1 _).mp hp)
      have ht := startup_expand_time W
      rw [reachesWithin_iff]
      refine ⟨2 * W + counterOverhead (Nat.bits W) (W + 1), ht, ?_, ?_, ?_⟩
      · intro s hs he
        exact hr.2 s hs he
      · intro s hs j
        have h := MultiTapeTM.workTapePos_runFrom_mem_Icc (expandTM 1 0 [false]) d s j
        rw [Finset.mem_Icc] at h
        change |((expandTM 1 0 [false]).runFrom d s).workTapePos j - d.workTapePos j| ≤
          ((8 * W + 2 : ℕ) : ℤ)
        rw [abs_le]
        constructor <;> omega
      · exact hr.1.trans (startupExpand_attach .done W d))
    (by
      intro x W d _ _
      simp only [startupAttach, startupExpandPost, Cfg.mapState_state, Option.map_some])

/-- The physical forecast of a word write, with its control tag supplied separately. -/
private def startupPatch {K : ℕ} {S : Type} {x : List Bool} (exit : S) (dst : Fin K)
    (w : List Bool) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with state := some exit, workTapes := wordWrite d dst w }

/-- A framed word write commutes with control erasure and attachment. -/
private theorem startupPatch_attach {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (dst : Fin K) (w : List Bool) (d : Turing.Cfg K Bool S x) : startupPatch exit dst w d =
      startupAttach exit (startupPatch () dst w (startupErase d)) := by
  rw [startupErase_eq]
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [startupPatch, startupAttach, wordWrite_apply,
      Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some]

/-- Copy any indexed word with the catalog contract, preserving its exact destination frame.

**Proof sketch.** Reindex `copyTM_contract` by the source word. Its precondition is the word
predicate after `startup_wordAt_erase`; its sweep endpoint is `startupPatch` by the published
sweep and word-write equations. The catalog's time is exactly twice the word length plus two. -/
private noncomputable def startupCopyStage {K : ℕ} {ι : Type} (src dst : Fin K)
    (hne : src ≠ dst) (word : List Bool → ι → List Bool) : StartupStage K ι :=
  StartupStage.ofContract (fun x => copyTM_contract src dst hne x) word
    (fun {x} i d => WordAt d src (word x i))
    (fun {x} i d => startupPatch () dst (word x i) d)
    (fun x i => 2 * (word x i).length + 2)
    (by
      intro x i d _ hp
      rw [copyTM_contract_pre]
      exact (wordAt_iff _ _ _).mp ((startup_wordAt_erase d src _).mp hp))
    (by
      intro x i d
      have he : (copyTM_contract src dst hne x).post (word x i) d =
          startupPatch SweepPhase.done dst (word x i) d := by
        apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
          simp only [copyTM_contract_post, sweepPost_state, sweepPost_inputPos,
            sweepPost_workTapes, sweepPost_workTapePos, sweepPost_output,
            startupPatch, wordWrite_apply]
      exact he.trans (startupPatch_attach .done dst _ d))
    (by intro x i d _ _; rw [copyTM_contract_time])

/-- The physical forecast of rewinding one full word from its right delimiter. -/
private def startupRewindPost {K : ℕ} {S : Type} {x : List Bool} (exit : S) (j : Fin K)
    (w : List Bool) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with
    state := some exit
    workTapePos := Function.update d.workTapePos j (d.workTapePos j - (w.length : ℤ)) }

/-- Rewinding's head update commutes with erasing and reattaching the control tag. -/
private theorem startupRewind_attach {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (j : Fin K) (w : List Bool) (d : Turing.Cfg K Bool S x) : startupRewindPost exit j w d =
      startupAttach exit (startupRewindPost () j w (startupErase d)) := by
  apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
    simp only [startupRewindPost, startupAttach, startupErase, Function.update_apply,
      Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some]

/-- The catalog's framed rewind as a startup stage; the empty word is included.

**Proof sketch.** Apply `rewindTM_run_ofCfg` with the full word length. Its exact time and cut
are packaged with `StartupStage.ofRow`, and the universal head-speed bound supplies a
sufficient linear work radius. `startupRewind_attach` identifies the physical endpoint. -/
private noncomputable def startupRewindStage {K : ℕ} {ι : Type} (j : Fin K)
    (word : List Bool → ι → List Bool) : StartupStage K ι :=
  StartupStage.ofRow (rewindTM K j) .start .done
    (fun {x} i d => ∀ p : ℤ, -1 ≤ p → p < ((word x i).length : ℤ) →
      d.workTapes j (d.workTapePos j - (word x i).length + p) = FinTM.bufferTape (word x i) p)
    (fun {x} i d => startupRewindPost () j (word x i) d)
    (fun x i => (word x i).length + 2) (fun x i => (word x i).length + 2)
    (by
      intro x i d hd hp
      have hw : ∀ p : ℤ, -1 ≤ p → p < ((word x i).length : ℤ) →
          d.workTapes j (d.workTapePos j - (word x i).length + p) = FinTM.bufferTape (word x i) p := by
        intro p h₁ h₂
        simpa only [startupErase, Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hp p h₁ h₂
      obtain ⟨run, cut, -⟩ := rewindTM_run_ofCfg j (word x i) (word x i).length le_rfl d hd hw
      rw [reachesWithin_iff]
      refine ⟨(word x i).length + 2, le_rfl, ?_, ?_, ?_⟩
      · intro s hs he
        exact cut s hs he
      · intro s hs a
        have h := MultiTapeTM.workTapePos_runFrom_mem_Icc (rewindTM K j) d s a
        rw [Finset.mem_Icc] at h
        change |((rewindTM K j).runFrom d s).workTapePos a - d.workTapePos a| ≤
          (((word x i).length + 2 : ℕ) : ℤ)
        rw [abs_le]
        constructor <;> omega
      · exact run.trans (startupRewind_attach RewindPhase.done j (word x i) d))
    (by
      intro x i d _ _
      simp only [startupAttach, startupRewindPost, Cfg.mapState_state, Option.map_some])

/-- Clear an indexed word by the catalog sweep while retaining its interval frame.

**Proof sketch.** Reindex `clearTM_contract` by the word and use `wordAt_iff` to remove the
control erasure from its precondition. The published sweep field readers identify its
physical forecast, and the catalog time reader gives twice the word length plus two. -/
private noncomputable def startupClearStage {K : ℕ} {ι : Type} (j : Fin K)
    (word : List Bool → ι → List Bool) : StartupStage K ι :=
  StartupStage.ofContract (fun x => clearTM_contract j x) word
    (fun {x} i d => WordAt d j (word x i))
    (fun {x} i d => sweepPost () j (fun _ _ _ _ => none) (word x i) d)
    (fun x i => 2 * (word x i).length + 2)
    (by
      intro x i d _ hp
      rw [clearTM_contract_pre]
      exact (wordAt_iff _ _ _).mp ((startup_wordAt_erase d j _).mp hp))
    (by
      intro x i d
      rw [startupErase_eq]
      apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
        simp only [startupAttach, clearTM_contract_post, sweepPost_state, sweepPost_inputPos,
          sweepPost_workTapes, sweepPost_workTapePos, sweepPost_output,
          Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some])
    (by intro x i d _ _; rw [clearTM_contract_time])

/-- Return from one cell beyond a word's right delimiter with the catalog backward skip.

**Proof sketch.** Reindex `skipBackTM_contract` by the ending word. Its precondition reads
only tapes and heads, which erasure preserves. Its published seek endpoint and time readers
give the returning head update and the word length plus three. -/
private noncomputable def startupSkipBackStage {K : ℕ} {ι : Type} (j : Fin K)
    (word : List Bool → ι → List Bool) : StartupStage K ι :=
  StartupStage.ofContract (fun x => skipBackTM_contract j x) word
    (fun {x} i d => ∀ p : ℤ, -1 ≤ p → p ≤ ((word x i).length : ℤ) →
      d.workTapes j (d.workTapePos j - (word x i).length - 1 + p) = FinTM.bufferTape (word x i) p)
    (fun {x} i d => seekPost () j (d.workTapePos j - (word x i).length - 1) d)
    (fun x i => (word x i).length + 3)
    (by
      intro x i d _ hp
      rw [skipBackTM_contract_pre]
      simpa only [startupErase, Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hp)
    (by
      intro x i d
      rw [startupErase_eq]
      apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
        simp only [startupAttach, skipBackTM_contract_post, seekPost_state, seekPost_inputPos,
          seekPost_workTapes, seekPost_workTapePos, seekPost_output,
          Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some])
    (by intro x i d _ _; rw [skipBackTM_contract_time])

/-- The advancing writer's physical forecast. -/
private def startupAdvancePost {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (j : Fin K) (w : List Bool) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with
    state := some exit
    workTapes := wordWrite d j w
    workTapePos := Function.update d.workTapePos j (d.workTapePos j + w.length) }

/-- Use the shared positive-return release for a fixed advancing writer.

**Proof sketch.** `writeAdvTM_run_ofCfg` is a positive return to its anchor. Package exactly
that row as a `ReturnContract`, including its head intervals, then apply
`ReturnContract.release`. The published release field equations give a fresh entry and a
first exit at the same time, with the advancing word-write forecast. -/
private noncomputable def startupWriteAdvanceStage {K : ℕ} (j : Fin K) (w : List Bool) :
    StartupStage K ℕ := by
  let C (x : List Bool) : ReturnContract (writeAdvTM K j w) 0 ℕ x := {
    pre := fun _ _ => True
    time := fun _ _ => w.length + 1
    post := fun _ d => startupAdvancePost 0 j w d
    lo := fun _ d => d.workTapePos
    hi := fun _ d a => d.workTapePos a + if a = j then (w.length : ℤ) else 0
    pos := by intro i d hd hp; omega
    run := by
      intro i d hd _
      rw [(writeAdvTM_run_ofCfg j w d hd).1]
      apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
        simp only [startupAdvancePost, wordWrite_apply]
    exit_eq := by intro i d hd hp; rfl
    cut := by intro i d hd hp; exact (writeAdvTM_run_ofCfg j w d hd).2.1
    env := by
      intro i d hd hp u hu a
      have h := (writeAdvTM_run_ofCfg j w d hd).2.2 a u hu
      by_cases ha : a = j
      · simpa only [ha, if_true] using h
      · simp only [ha, if_false] at h ⊢
        rw [h]
        simp only [add_zero, Finset.mem_Icc, le_refl, and_self] }
  exact StartupStage.ofContract (fun x => (C x).release) (fun _ i => i)
    (fun _ _ => True) (fun _ d => startupAdvancePost () j w d)
    (fun _ _ => w.length + 1)
    (by intro x i d _ _; rw [ReturnContract.release_pre]; trivial)
    (by
      intro x i d
      rw [ReturnContract.release_post, startupErase_eq]
      have hm : d.mapState (fun _ => (0 : Fin (w.length + 1))) =
          ⟨d.state.map (fun _ => 0), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
        apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
          simp only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
            Cfg.mapState_workTapePos, Cfg.mapState_output]
      rw [hm]
      apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
        simp only [C, startupAdvancePost, startupAttach, wordWrite_apply,
          Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some, Function.update_apply])
    (by intro x i d _ _; rw [ReturnContract.release_time])

/-- The shared walk's physical forecast for a set of work heads. -/
private def startupWalkPost {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (moved : Fin K → Prop) [DecidablePred moved] (w : List Bool)
    (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with
    state := some exit
    workTapePos := fun j => d.workTapePos j + if moved j then ((w.length + 1 : ℕ) : ℤ) else 0 }

/-- Walk selected heads across a guide word, including its right blank. -/
private noncomputable def startupWalkStage {K : ℕ} (src : Fin K)
    (moved : Fin K → Prop) [DecidablePred moved] (hsrc : moved src)
    (word : List Bool → ℕ → List Bool) : StartupStage K ℕ :=
  StartupStage.ofContract (fun x => walkTM_contract src moved hsrc .pos x) word
    (fun {x} W d => WordAt d src (word x W))
    (fun {x} W d => startupWalkPost () moved (word x W) d)
    (fun x W => (word x W).length + 1)
    (by
      intro x W d _ hp
      rw [walkTM_contract_pre]
      intro p hp'
      have hw := (wordAt_iff _ _ _).mp ((startup_wordAt_erase d src _).mp hp)
        p (by omega) (by exact_mod_cast hp')
      simpa only [SignType.pos_eq_one, SignType.coe_one, one_mul, FinTM.bufferTape_nat] using hw)
    (by
      intro x W d
      rw [startupErase_eq]
      apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
        simp only [walkTM_contract_post, startupWalkPost, startupAttach,
          Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some,
          SignType.pos_eq_one, SignType.coe_one, one_mul, Nat.cast_add, Nat.cast_one])
    (by intro x W d _ _; rw [walkTM_contract_time])

/-- Erase the cell immediately before the current head and restore the head. -/
private def startupErasePreviousPost {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (j : Fin K) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with
    state := some exit
    workTapes := Function.update d.workTapes j
      (Function.update (d.workTapes j) (d.workTapePos j - 1) none) }

/-- There is no catalog row for erasing the previous cell and returning in place. This fixed
two-action leaf moves left, erases, and moves right; the surrounding walks remain catalog rows. -/
private def startupErasePreviousTM {K : ℕ} (j : Fin K) : MultiTapeTM K Bool (Fin 3) where
  q₀ := 0
  tr q _ _ := if q = 0 then tapeAction j 0 none .neg 1
    else tapeAction j 0 (some none) .pos 2

/-- The two fixed actions erase exactly the previous cell and first reach the exit at two.

**Proof sketch.** Apply the published one-tape move and write step equations. The first
configuration has head `pos - 1`; the second writes there and restores `pos`. The only
earlier configurations have states zero and one, so neither is the exit two. -/
private theorem startupErasePrevious_run {K : ℕ} {x : List Bool} (j : Fin K)
    (d : Turing.Cfg K Bool (Fin 3) x) (hd : d.state = some 0) :
    (startupErasePreviousTM j).runFrom d 2 = startupErasePreviousPost 2 j d ∧
    ∀ s < 2, ((startupErasePreviousTM j).runFrom d s).state ≠ some 2 := by
  let d₁ : Turing.Cfg K Bool (Fin 3) x :=
    {d with
      state := some 1
      workTapePos := Function.update d.workTapePos j (d.workTapePos j - 1)}
  have h₁ : (startupErasePreviousTM j).runFrom d 1 = d₁ := by
    rw [MultiTapeTM.runFrom_one, step_of_tapeAction_move _ _ j 0 .neg hd rfl,
      moveInputPos_zero]
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one, sub_eq_add_neg, d₁]
  constructor
  · change (startupErasePreviousTM j).runFrom d (1 + 1) = startupErasePreviousPost 2 j d
    rw [MultiTapeTM.runFrom_succ_eq_step', h₁,
      step_of_tapeAction_write _ _ j 0 none .pos (show d₁.state = some 1 from rfl) rfl,
      moveInputPos_zero]
    apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
      simp [d₁, startupErasePreviousPost, SignType.pos_eq_one, Function.update_apply]
    split_ifs <;> simp_all
  · intro s hs
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp [MultiTapeTM.runFrom_zero, hd]
    · rw [h₁]
      simp [d₁]

/-- The fixed erasure forecast commutes with erasing and reattaching finite control. -/
private theorem startupErasePrevious_attach {K : ℕ} {S : Type} {x : List Bool}
    (exit : S) (j : Fin K) (d : Turing.Cfg K Bool S x) :
    startupErasePreviousPost exit j d =
      startupAttach exit (startupErasePreviousPost () j (startupErase d)) := by
  rw [startupErase_eq]
  apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
    simp only [startupErasePreviousPost, startupAttach, Function.update_apply,
      Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some]

/-- The previous-cell erasure as a two-step startup stage.

**Proof sketch.** Package `startupErasePrevious_run` through `StartupStage.ofRow` and use
the universal head-speed bound for the two-step radius. The attachment lemma gives the
physical forecast with the stage's exit tag. -/
private noncomputable def startupErasePreviousStage {K : ℕ} (j : Fin K) : StartupStage K ℕ :=
  StartupStage.ofRow (startupErasePreviousTM j) 0 2 (fun _ _ => True)
    (fun _ d => startupErasePreviousPost () j d) (fun _ _ => 2) (fun _ _ => 2)
    (by
      intro x W d hd _
      obtain ⟨run, cut⟩ := startupErasePrevious_run j d hd
      rw [reachesWithin_iff]
      refine ⟨2, le_rfl, fun s hs he => cut s hs (Set.mem_singleton_iff.mp he), ?_, ?_⟩
      · intro s hs a
        have h := MultiTapeTM.workTapePos_runFrom_mem_Icc (startupErasePreviousTM j) d s a
        rw [Finset.mem_Icc] at h
        change |((startupErasePreviousTM j).runFrom d s).workTapePos a - d.workTapePos a| ≤ (2 : ℤ)
        rw [abs_le]
        constructor <;> omega
      · exact run.trans (startupErasePrevious_attach (2 : Fin 3) j d))
    (by
      intro x W d _ _
      simp only [startupErasePreviousPost, startupAttach, Cfg.mapState_state, Option.map_some])

/-! ## Private native-input stages -/

/-- The forecast of a native input-head change with all work data kept. -/
private def startupInputPost {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (ip : Fin (x.length + 2)) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  { d with state := some exit, inputPos := ip }

/-- An input-only change commutes with erasing and reattaching the control tag. -/
private theorem startupInputPost_attach {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (ip : Fin (x.length + 2)) (d : Turing.Cfg K Bool S x) : startupInputPost exit ip d =
      startupAttach exit (startupInputPost () ip (startupErase d)) := by
  rw [startupErase_eq]
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [startupInputPost, startupAttach, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some]

/-- The shared rewind expects a positive input position. No catalog leaf advances just the
native input head once and returns; this leaf supplies that single fixed input action. -/
private def startupAdvanceInputTM (K : ℕ) : MultiTapeTM K Bool Bool where
  q₀ := false
  tr := fun q _ _ => inputMoveAction (if q then 0 else .pos) true

/-- Advance the native input head once, with zero work radius.

**Proof sketch.** Apply `step_of_inputMoveAction` to the fixed leaf. Its first successor is
the exit, distinct from the entry, and both configurations have the original work heads.
Package that one-step run through `StartupStage.ofRow` with work radius zero. -/
private noncomputable def startupAdvanceInputStage (K : ℕ) : StartupStage K ℕ :=
  StartupStage.ofRow (startupAdvanceInputTM K) false true (fun _ _ => True)
    (fun _ d => startupInputPost () (moveInputPos d.inputPos .pos) d)
    (fun _ _ => 1) (fun _ _ => 0)
    (by
      intro x i d hd _
      have hs : (startupAdvanceInputTM K).runFrom d 1 =
          startupInputPost true (moveInputPos d.inputPos .pos) d := by
        rw [MultiTapeTM.runFrom_one, step_of_inputMoveAction _ _ .pos hd rfl]
        rfl
      rw [reachesWithin_iff]
      refine ⟨1, le_rfl, ?_, ?_, ?_⟩
      · intro s ht he
        obtain rfl : s = 0 := by omega
        simp only [MultiTapeTM.runFrom_zero, hd, Set.mem_singleton_iff, Option.some.injEq,
          Bool.false_eq_true] at he
      · intro s ht j
        rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
        · simp only [MultiTapeTM.runFrom_zero, sub_self, abs_zero, Nat.cast_zero, le_refl]
        · rw [hs]
          simp only [startupInputPost, sub_self, abs_zero, Nat.cast_zero, le_refl]
      · have hi : (startupErase d).inputPos = d.inputPos := by
          rw [startupErase, Cfg.mapState_inputPos]
        change (startupAdvanceInputTM K).runFrom d 1 = startupAttach true
          (startupInputPost () (moveInputPos (startupErase d).inputPos .pos) (startupErase d))
        rw [hi]
        exact hs.trans (startupInputPost_attach true _ d))
    (by
      intro x i d _ _
      simp only [startupInputPost, startupAttach, Cfg.mapState_state, Option.map_some])

/-- A clamped right step is always at a positive native input position. -/
private theorem startup_advance_positive {n : ℕ} (p : Fin (n + 2)) :
    1 ≤ (moveInputPos p .pos).val := by
  by_cases hp : p.val = n + 1
  · have he : p = (⟨n + 1, by omega⟩ : Fin (n + 2)) := Fin.ext hp
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    omega
  · rw [moveInputPos_pos_of_ne_right p hp]
    change 1 ≤ p.val + 1
    omega

/-- Rewind only the native input head, retaining the shared row's zero work radius.

**Proof sketch.** `inputRewindTM_run` supplies the exact first return and its unchanged work
heads. Its time is at most `|x| + 2`, because the native position is at most `|x| + 1`.
Package that row with radius zero, rather than its linear time bound. -/
private noncomputable def startupInputRewindStage (K : ℕ) : StartupStage K ℕ :=
  StartupStage.ofRow (inputRewindTM K) .start .done
    (fun _ d => 1 ≤ d.inputPos.val) (fun _ d => startupInputPost () 1 d)
    (fun x _ => x.length + 2) (fun _ _ => 0)
    (by
      intro x i d hd hp
      have hp' : 1 ≤ d.inputPos.val := by
        simpa only [startupErase, Cfg.mapState_inputPos] using hp
      obtain ⟨run, cut, frame⟩ := inputRewindTM_run d hd hp'
      rw [reachesWithin_iff]
      refine ⟨d.inputPos.val + 1, ?_, ?_, ?_, ?_⟩
      · change d.inputPos.val + 1 ≤ x.length + 2
        have := d.inputPos.isLt
        omega
      · intro s hs he; exact cut s hs (Set.mem_singleton_iff.mp he)
      · intro s hs j
        rw [congrFun (frame s hs).2.1 j]
        simp only [sub_self, abs_zero, Nat.cast_zero, le_refl]
      · exact run.trans (startupInputPost_attach InputRewindPhase.done 1 d))
    (by
      intro x i d _ _
      simp only [startupInputPost, startupAttach, Cfg.mapState_state, Option.map_some])

/-- The two native positioning stages do not move any work head.

**Proof sketch.** The one-step stage has only its start and successor, both with unchanged
work heads. For rewind, the contract's strict cut bounds its chosen time by the public row's
first exit time. Apply that row's unchanged-head clause throughout the chosen interval. -/
private theorem startup_native_position_radius (K : ℕ) :
    (startupAdvanceInputStage K).Radius (fun _ _ => 0) ∧
    (startupInputRewindStage K).Radius (fun _ _ => 0) := by
  constructor
  · intro x i d hd hp u hu j
    have ht := (startupAdvanceInputStage K).time_le i d hd hp
    change ( (startupAdvanceInputStage K).C x).time i d ≤ 1 at ht
    rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
    · simp only [MultiTapeTM.runFrom_zero, sub_self, abs_zero, Nat.cast_zero, le_refl]
    · change |((startupAdvanceInputTM K).runFrom d 1).workTapePos j - d.workTapePos j| ≤ (0 : ℤ)
      rw [MultiTapeTM.runFrom_one, step_of_inputMoveAction _ _ .pos hd rfl]
      simp only [sub_self, abs_zero, le_refl]
  · intro x i d hd hp u hu j
    have hp' : 1 ≤ d.inputPos.val := by
      simpa only [startupInputRewindStage, StartupStage.ofRow, StartupStage.ofContract,
        startupErase, Cfg.mapState_inputPos] using hp
    obtain ⟨run, _, frame⟩ := inputRewindTM_run d hd hp'
    have ht : ((startupInputRewindStage K).C x).time i d ≤ d.inputPos.val + 1 := by
      by_contra hgt
      have hc := ((startupInputRewindStage K).C x).cut i d hd
        (((startupInputRewindStage K).pre_eq i d).mpr hp) (d.inputPos.val + 1) (by omega)
      apply hc
      change ((inputRewindTM K).runFrom d (d.inputPos.val + 1)).state ∈ {some InputRewindPhase.done}
      rw [run]
      exact Set.mem_singleton _
    change |((inputRewindTM K).runFrom d u).workTapePos j - d.workTapePos j| ≤ (0 : ℤ)
    rw [congrFun (frame u (hu.trans ht)).2.1 j]
    simp only [sub_self, abs_zero, le_refl]

/-- Count the input length in a blank selected bank, preserving the published small radius.

**Proof sketch.** Choose `exists_inputLengthTM` and strengthen its blank-interval assumptions
to globally blank tapes. Its exact endpoint is a word patch by `wordWrite_apply`. Package the
row with its linear time and logarithmic radius separately; the `ofReaches` envelope readers
retain that radius at the chosen contract time. -/
private theorem startup_length_stage :
    ∃ (K : ℕ) (T : StartupStage (K + 1) ℕ) (C : ℕ),
      (∀ {x} i (d : Turing.Cfg (K + 1) Bool Unit x),
        T.pre i d ↔ d.inputPos = 1 ∧ ∀ j q, d.workTapes j q = none) ∧
      (∀ {x} i (d : Turing.Cfg (K + 1) Bool Unit x),
        T.next i d = startupPatch () 0 (Nat.bits x.length) d) ∧
      (∀ x i, T.bound x i = C * (x.length + 1)) ∧
      T.Radius (fun x _ => C * ((Nat.bits x.length).length + 1)) := by
  obtain ⟨K, S, hS, hD, M, entry, exit, C, row⟩ := exists_inputLengthTM
  letI := hS
  letI := hD
  let P := fun {x : List Bool} (_ : ℕ) (d : Turing.Cfg (K + 1) Bool Unit x) =>
    d.inputPos = 1 ∧ ∀ j q, d.workTapes j q = none
  let F := fun {x : List Bool} (_ : ℕ) (d : Turing.Cfg (K + 1) Bool Unit x) =>
    startupPatch () 0 (Nat.bits x.length) d
  have hr : ∀ {x} i (d : Turing.Cfg (K + 1) Bool S x), d.state = some entry →
      P i (startupErase d) → ReachesWithin M d {some exit} (C * (x.length + 1))
        (C * ((Nat.bits x.length).length + 1)) (startupAttach exit (F i (startupErase d))) := by
    intro x i d hd hp
    have hP : d.inputPos = 1 ∧ ∀ j q, d.workTapes j q = none := by
      simpa only [P, startupErase, Cfg.mapState_inputPos, Cfg.mapState_workTapes] using hp
    obtain ⟨t, ht, cut, env, run⟩ := row d hd hP.1
      (fun p _ _ => hP.2 0 _) (fun j _ p => hP.2 j p)
    rw [reachesWithin_iff]
    refine ⟨t, ht, fun s hs he => cut s hs (Set.mem_singleton_iff.mp he), env, ?_⟩
    have he : M.runFrom d t = startupPatch exit 0 (Nat.bits x.length) d := by
      rw [run]
      apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
        simp only [startupPatch, wordWrite_apply]
    exact he.trans (startupPatch_attach exit 0 (Nat.bits x.length) d)
  have hx : ∀ {x} i (d : Turing.Cfg (K + 1) Bool S x), d.state = some entry →
      P i (startupErase d) → (startupAttach exit (F i (startupErase d))).state = some exit := by
    intro x i d _ _
    simp only [F, startupPatch, startupAttach, Cfg.mapState_state, Option.map_some]
  let T := StartupStage.ofRow M entry exit P F (fun x _ => C * (x.length + 1))
    (fun x _ => C * ((Nat.bits x.length).length + 1)) hr hx
  refine ⟨K, T, C, fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  apply StartupStage.radius_of_box
  · intro x i d j
    simp only [T, StartupStage.ofRow, StartupStage.ofContract, Contract.ofReaches_lo]
  · intro x i d j
    simp only [T, StartupStage.ofRow, StartupStage.ofContract, Contract.ofReaches_hi]

/-! ## Private preparation templates -/

/-- A bank of finite words with specified heads and empty physical output. -/
private def startupWords {K : ℕ} {x : List Bool} (ws : Fin K → List Bool)
    (heads : Fin K → ℤ) (ip : Fin (x.length + 2)) : Turing.Cfg K Bool Unit x :=
  ⟨some (), ip, fun j => FinTM.bufferTape (ws j), heads, []⟩

/-- Read a word bank as a template indexed by the width and the input. -/
private def startupWordsTemplate {K : ℕ} (ws : List Bool → ℕ → Fin K → List Bool)
    (heads : List Bool → ℕ → Fin K → ℤ) : StartupTemplate K :=
  fun {x} W ip => startupWords (ws x W) (heads x W) ip

/-- A word at head zero is delimited in the canonical bank. -/
private theorem startupWords_wordAt {K : ℕ} {x : List Bool} (ws : Fin K → List Bool)
    (heads : Fin K → ℤ) (ip : Fin (x.length + 2)) (j : Fin K) (hj : heads j = 0) :
    WordAt (startupWords ws heads ip) j (ws j) := by
  rw [wordAt_iff]
  intro p _ _
  simp only [startupWords, hj, zero_add]

/-- A prefix patch replaces that prefix and keeps the old word's suffix.

**Proof sketch.** Negative cells remain blank. At a nonnegative cell, split at the new
word's length: lookup in the concatenation uses the new prefix before the split and the
old word, through `List.getElem?_drop`, after it. -/
private theorem startup_buffer_patch (u w : List Bool) :
    wordPatch (FinTM.bufferTape u) 0 w = FinTM.bufferTape (w ++ u.drop w.length) := by
  funext q
  by_cases hq : 0 ≤ q
  · simp only [wordPatch_apply, zero_add, sub_zero, FinTM.bufferTape_eq, if_pos hq]
    by_cases h : q.toNat < w.length
    · rw [if_pos (by omega), List.getElem?_append_left h]
    · rw [if_neg (by omega), List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1
      omega
  · rw [wordPatch_of_not_mem _ _ _ (by omega), FinTM.bufferTape_of_neg _ (by omega),
      FinTM.bufferTape_of_neg _ (by omega)]

/-- Appending a patch at a finite buffer's end appends the word itself. -/
private theorem startup_buffer_append (u w : List Bool) :
    wordPatch (FinTM.bufferTape u) u.length w = FinTM.bufferTape (u ++ w) := by
  have hu : wordPatch (FinTM.bufferTape []) 0 u = FinTM.bufferTape u := by
    simpa only [List.drop_nil, List.append_nil] using startup_buffer_patch [] u
  calc
    _ = wordPatch (wordPatch (FinTM.bufferTape []) 0 u) (0 + u.length) w := by rw [hu]; simp
    _ = wordPatch (FinTM.bufferTape []) 0 (u ++ w) := wordPatch_append _ _ _ _
    _ = FinTM.bufferTape (u ++ w) := by
      simpa only [List.drop_nil, List.append_nil] using startup_buffer_patch [] (u ++ w)

/-- A word patch at head zero updates one finite word in the canonical bank.

**Proof sketch.** Outside the destination the word-write equation keeps the frame. On the
destination it is `startup_buffer_patch`, which replaces precisely the prefix interval.
The remaining configuration fields are unchanged. -/
private theorem startupWords_patch {K : ℕ} {x : List Bool} (ws : Fin K → List Bool)
    (heads : Fin K → ℤ) (ip : Fin (x.length + 2)) (j : Fin K) (w : List Bool)
    (hj : heads j = 0) :
    startupPatch () j w (startupWords ws heads ip) =
      startupWords (Function.update ws j (w ++ (ws j).drop w.length)) heads ip := by
  apply Turing.Cfg.ext
  · rfl
  · rfl
  · funext a q
    by_cases ha : a = j
    · subst a
      simp only [startupPatch, startupWords, wordWrite_apply, Function.update_self, true_and, hj]
      simpa only [wordPatch_apply] using congrFun (startup_buffer_patch (ws j) w) q
    · simp only [startupPatch, startupWords, wordWrite_apply, ha, false_and, if_false,
        Function.update_of_ne ha]
  · rfl
  · rfl

/-- Copy between two zero-headed finite words, retaining an arbitrary old destination suffix.

**Proof sketch.** The source buffer supplies the catalog copy precondition. Its endpoint is
`startupWords_patch`; the head vector is unchanged. Twice the source length plus two is
absorbed in the supplied linear coefficient. -/
private noncomputable def startupCopyRoute {K : ℕ}
    (ws : List Bool → ℕ → Fin K → List Bool) (heads : List Bool → ℕ → Fin K → ℤ)
    (src dst : Fin K) (hne : src ≠ dst)
    (hs : ∀ x W, heads x W src = 0) (hd : ∀ x W, heads x W dst = 0)
    (c : ℕ) (hlen : ∀ x W, (ws x W src).length ≤ c * (W + (Nat.bits x.length).length + 1)) :
    StartupRoute K (startupWordsTemplate ws heads)
      (startupWordsTemplate (fun x W => Function.update (ws x W) dst
        (ws x W src ++ (ws x W dst).drop (ws x W src).length)) heads) :=
  StartupRoute.ofStage _ _ (startupCopyStage src dst hne (fun x W => ws x W src))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun W ip => startupWords_wordAt _ _ ip src (hs _ W))
    (fun W ip => startupWords_patch _ _ ip dst _ (hd _ W))
    (2 * c + 2) (by
      intro x W
      change 2 * (ws x W src).length + 2 ≤ (2 * c + 2) * (W + (Nat.bits x.length).length + 1)
      have h := hlen x W
      nlinarith)

/-- Rewind a finite word from its right delimiter to head zero.

**Proof sketch.** The head hypothesis makes the shared rewind's origin zero. The full finite
buffer supplies every cell of its precondition. Its endpoint updates exactly that head to
zero, and its time is the word length plus two. -/
private noncomputable def startupRewindRoute {K : ℕ}
    (ws : List Bool → ℕ → Fin K → List Bool) (heads : List Bool → ℕ → Fin K → ℤ)
    (j : Fin K) (hj : ∀ x W, heads x W j = (ws x W j).length)
    (c : ℕ) (hlen : ∀ x W, (ws x W j).length ≤ c * (W + (Nat.bits x.length).length + 1)) :
    StartupRoute K (startupWordsTemplate ws heads)
      (startupWordsTemplate ws (fun x W => Function.update (heads x W) j 0)) :=
  StartupRoute.ofStage _ _ (startupRewindStage j (fun x W => ws x W j))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro x W ip
      change ∀ p : ℤ, -1 ≤ p → p < ((ws x W j).length : ℤ) →
        FinTM.bufferTape (ws x W j) (heads x W j - (ws x W j).length + p) =
          FinTM.bufferTape (ws x W j) p
      simp only [hj, sub_self, zero_add, implies_true])
    (by
      intro x W ip
      change startupRewindPost () j (ws x W j) (startupWords (ws x W) (heads x W) ip) = _
      simp only [startupRewindPost, startupWordsTemplate, startupWords, hj, sub_self])
    (c + 2) (by
      intro x W
      change (ws x W j).length + 2 ≤ (c + 2) * (W + (Nat.bits x.length).length + 1)
      have h := hlen x W
      nlinarith)

/-- Appending a fixed word advances exactly one head in the canonical word bank.

**Proof sketch.** At the destination, the old head is its word's length, so the word-write
equation is `startup_buffer_append`. Every other tape is the frame, and the only head update
adds the appended word's length. -/
private theorem startupWords_advance {K : ℕ} {x : List Bool} (ws : Fin K → List Bool)
    (heads : Fin K → ℤ) (ip : Fin (x.length + 2)) (j : Fin K) (w : List Bool)
    (hj : heads j = (ws j).length) :
    startupAdvancePost () j w (startupWords ws heads ip) =
      startupWords (Function.update ws j (ws j ++ w))
        (Function.update heads j (heads j + w.length)) ip := by
  apply Turing.Cfg.ext
  · rfl
  · rfl
  · funext a q
    by_cases ha : a = j
    · subst a
      simp only [startupAdvancePost, startupWords, wordWrite_apply, Function.update_self, true_and]
      rw [hj]
      simpa only [wordPatch_apply] using congrFun (startup_buffer_append (ws j) w) q
    · simp only [startupAdvancePost, startupWords, wordWrite_apply, ha, false_and, if_false,
        Function.update_of_ne ha]
  · rfl
  · rfl

/-- Append a fixed prefix with the released catalog writer. -/
private noncomputable def startupWriteAdvanceRoute {K : ℕ}
    (ws : List Bool → ℕ → Fin K → List Bool) (heads : List Bool → ℕ → Fin K → ℤ)
    (j : Fin K) (w : List Bool) (hj : ∀ x W, heads x W j = (ws x W j).length) :
    StartupRoute K (startupWordsTemplate ws heads)
      (startupWordsTemplate (fun x W => Function.update (ws x W) j (ws x W j ++ w))
        (fun x W => Function.update (heads x W) j (heads x W j + w.length))) :=
  StartupRoute.ofStage _ _ (startupWriteAdvanceStage j w)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => trivial)
    (fun W ip => startupWords_advance _ _ ip j w (hj _ W))
    (w.length + 1) (by
      intro x W
      change w.length + 1 ≤ (w.length + 1) * (W + (Nat.bits x.length).length + 1)
      nlinarith)

/-- Select two distinct physical tapes, with destination first and counter second. -/
private def startupPair {K : ℕ} (a b : Fin K) (hne : a ≠ b) : Fin 2 ↪ Fin K where
  toFun j := if j = 0 then a else b
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Expanding into the end of a finite word appends zeroes and exhausts the binary counter.

**Proof sketch.** Reconstruct the forwarding embedding with `embedEmitCfg_eq`. On its first
tape, `startup_buffer_append` identifies the appended zero word. On its second, the published
constant-patch equation and `startup_buffer_patch` identify the exhausted counter. Off the
two selected tapes the reconstruction hypothesis is precisely the unchanged frame. -/
private theorem startupWords_expand {K : ℕ} {x : List Bool} (ws : Fin K → List Bool)
    (heads : Fin K → ℤ) (ip : Fin (x.length + 2)) (dst ctr : Fin K) (hne : dst ≠ ctr)
    (W : ℕ) (hd : heads dst = (ws dst).length) (hc : heads ctr = 0)
    (hw : ws ctr = Nat.bits W) :
    (startupExpandStage.embed (startupPair dst ctr hne)).next W (startupWords ws heads ip) =
      startupWords
        (Function.update (Function.update ws dst (ws dst ++ List.replicate W false))
          ctr (List.replicate (Nat.bits W).length true))
        (Function.update heads dst (heads dst + W)) ip := by
  let σ := startupPair dst ctr hne
  change embedEmitCfg σ _ _ _
    (startupExpandPost () W ((startupWords ws heads ip).select σ)) = _
  apply embedEmitCfg_eq
  · simp [startupExpandPost, Cfg.select_eq, startupWords]
  · simp [startupExpandPost, Cfg.select_eq, startupWords]
  · simp [startupExpandPost, Cfg.select_eq, startupWords]
  · intro i
    fin_cases i
    · constructor
      · funext q
        simp [σ, startupPair, startupExpandPost, Cfg.select_eq, startupWords,
          Fin.zero_eta, Function.Embedding.coeFn_mk,
          Function.update_apply, hne, ↓reduceIte]
        rw [hd]
        exact congrFun (startup_buffer_append (ws dst) (List.replicate W false)) q
      · simp [σ, startupPair, startupExpandPost, Cfg.select_eq, startupWords,
          Function.Embedding.coeFn_mk, Function.update_apply, ↓reduceIte]
    · constructor
      · funext q
        have ht := congrFun (startup_buffer_patch (Nat.bits W)
          (List.replicate (Nat.bits W).length true)) q
        simp [List.length_replicate, List.drop_length, List.append_nil,
          wordPatch_replicate, zero_add] at ht
        simpa [σ, startupPair, startupExpandPost, Cfg.select_eq, startupWords,
          Function.Embedding.coeFn_mk, Function.update_apply, ↓reduceIte,
          hne, Ne.symm hne, hc, hw, zero_add] using ht
      · simp [σ, startupPair, startupExpandPost, Cfg.select_eq, startupWords,
          Function.Embedding.coeFn_mk, Function.update_apply, ↓reduceIte,
          Ne.symm hne]
  · intro j hj
    have hdst : j ≠ dst := by
      intro he
      apply hj
      refine ⟨0, ?_⟩
      simpa [σ, startupPair, Function.Embedding.coeFn_mk] using he.symm
    have hctr : j ≠ ctr := by
      intro he
      apply hj
      refine ⟨1, ?_⟩
      simpa [σ, startupPair, Function.Embedding.coeFn_mk, ↓reduceIte] using he.symm
    simp [startupWords, Function.update_of_ne hdst, Function.update_of_ne hctr,
      and_self]

/-- Append `W` zeroes through the shared two-tape counter-loop expansion. -/
private noncomputable def startupExpandRoute {K : ℕ}
    (ws : List Bool → ℕ → Fin K → List Bool) (heads : List Bool → ℕ → Fin K → ℤ)
    (dst ctr : Fin K) (hne : dst ≠ ctr)
    (hd : ∀ x W, heads x W dst = (ws x W dst).length)
    (hc : ∀ x W, heads x W ctr = 0) (hw : ∀ x W, ws x W ctr = Nat.bits W) :
    StartupRoute K (startupWordsTemplate ws heads)
      (startupWordsTemplate
        (fun x W => Function.update (Function.update (ws x W) dst
          (ws x W dst ++ List.replicate W false)) ctr (List.replicate (Nat.bits W).length true))
        (fun x W => Function.update (heads x W) dst (heads x W dst + W))) :=
  StartupRoute.ofStage _ _ (startupExpandStage.embed (startupPair dst ctr hne))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (by
      intro x W ip
      change WordAt ((startupWords (ws x W) (heads x W) ip).select (startupPair dst ctr hne))
        1 (Nat.bits W)
      rw [wordAt_iff]
      intro p _ _
      simp [Cfg.select_eq, startupWords, startupPair, Function.Embedding.coeFn_mk,
        Fin.isValue, ↓reduceIte, hc, hw, zero_add])
    (fun W ip => startupWords_expand _ _ ip dst ctr hne W (hd _ W) (hc _ W) (hw _ W))
    10 (by
      intro x W
      change 8 * W + 2 ≤ 10 * (W + (Nat.bits x.length).length + 1)
      omega)


/-- The preparation bank initially holds the input length on tape five and the captured width
on tape eight; tape nine is a reusable expansion counter. -/
private def startupSeedWords (x : List Bool) (W : ℕ) : Fin 10 → List Bool :=
  Function.update (Function.update (fun _ => []) 5 (Nat.bits x.length)) 8 (Nat.bits W)

/-- The captured width's head starts at its right delimiter. -/
private def startupSeedHeads (_x : List Bool) (W : ℕ) : Fin 10 → ℤ :=
  Function.update (fun _ => 0) 8 (Nat.bits W).length

/-- The finite word bank after allocating the registers, key and empty table header. -/
private def startupRegisterWords (a : ℕ) (x : List Bool) (W : ℕ) : Fin 10 → List Bool :=
  ![[true], List.replicate (W + a) false, List.replicate W false, List.replicate W false,
    List.replicate W false, Nat.bits x.length, [], [], Nat.bits W,
    List.replicate (Nat.bits W).length true]

set_option linter.unusedSimpArgs false in
/-- Allocate the zero registers, the extended key and the empty table's header.

**Proof sketch.** Rewind the width master, copy it to the reusable counter, expand register
two and rewind it, then copy it into registers three and four. Write the key's fixed prefix,
restore the counter, expand its variable suffix and rewind the whole key. Write and rewind
the table header. Every call is one of the preceding catalog routes; normalize the final
word and head vectors cell by cell. The route compositions retain the linear time bound. -/
private noncomputable def startupRegisterRoute (a : ℕ) :
    StartupRoute 10 (startupWordsTemplate startupSeedWords startupSeedHeads)
      (startupWordsTemplate (startupRegisterWords a) (fun _ _ _ => 0)) := by
  let w0 := startupSeedWords
  let h0 := startupSeedHeads
  let h1 := fun x W => Function.update (h0 x W) (8 : Fin 10) 0
  let r1 := startupRewindRoute w0 h0 8
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads]) (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads] ; nlinarith)
  let c1 := r1
  let w2 := fun x W => Function.update (w0 x W) (9 : Fin 10)
    (w0 x W 8 ++ (w0 x W 9).drop (w0 x W 8).length)
  let r2 := startupCopyRoute w0 h1 8 9 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1])
    (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1] ; nlinarith)
  let c2 := c1.seq r2
  let w3 := fun x W => Function.update (Function.update (w2 x W) (2 : Fin 10)
    (w2 x W 2 ++ List.replicate W false)) 9 (List.replicate (Nat.bits W).length true)
  let h3 := fun x W => Function.update (h1 x W) (2 : Fin 10) (h1 x W 2 + W)
  let r3 := startupExpandRoute w2 h1 2 9 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2])
  let c3 := c2.seq r3
  let h4 := fun x W => Function.update (h3 x W) (2 : Fin 10) 0
  let r4 := startupRewindRoute w3 h3 2
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3]) (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3] ; nlinarith)
  let c4 := c3.seq r4
  let w5 := fun x W => Function.update (w3 x W) (3 : Fin 10)
    (w3 x W 2 ++ (w3 x W 3).drop (w3 x W 2).length)
  let r5 := startupCopyRoute w3 h4 2 3 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4])
    (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4] ; nlinarith)
  let c5 := c4.seq r5
  let w6 := fun x W => Function.update (w5 x W) (4 : Fin 10)
    (w5 x W 2 ++ (w5 x W 4).drop (w5 x W 2).length)
  let r6 := startupCopyRoute w5 h4 2 4 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5])
    (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5] ; nlinarith)
  let c6 := c5.seq r6
  let w7 := fun x W => Function.update (w6 x W) (1 : Fin 10) (w6 x W 1 ++ List.replicate a false)
  let h7 := fun x W => Function.update (h4 x W) (1 : Fin 10) (h4 x W 1 + (List.replicate a false).length)
  let r7 := startupWriteAdvanceRoute w6 h4 1 (List.replicate a false)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6])
  let c7 := c6.seq r7
  let w8 := fun x W => Function.update (w7 x W) (9 : Fin 10)
    (w7 x W 8 ++ (w7 x W 9).drop (w7 x W 8).length)
  let r8 := startupCopyRoute w7 h7 8 9 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7])
    (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7] ; nlinarith)
  let c8 := c7.seq r8
  let w9 := fun x W => Function.update (Function.update (w8 x W) (1 : Fin 10)
    (w8 x W 1 ++ List.replicate W false)) 9 (List.replicate (Nat.bits W).length true)
  let h9 := fun x W => Function.update (h7 x W) (1 : Fin 10) (h7 x W 1 + W)
  let r9 := startupExpandRoute w8 h7 1 9 (by decide)
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8]) (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8])
  let c9 := c8.seq r9
  let h10 := fun x W => Function.update (h9 x W) (1 : Fin 10) 0
  let r10 := startupRewindRoute w9 h9 1
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9]) (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9] ; nlinarith)
  let c10 := c9.seq r10
  let w11 := fun x W => Function.update (w9 x W) (0 : Fin 10) (w9 x W 0 ++ [true])
  let h11 := fun x W => Function.update (h10 x W) (0 : Fin 10) (h10 x W 0 + ([true]).length)
  let r11 := startupWriteAdvanceRoute w9 h10 0 ([true])
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9, h10])
  let c11 := c10.seq r11
  let h12 := fun x W => Function.update (h11 x W) (0 : Fin 10) 0
  let r12 := startupRewindRoute w11 h11 0
    (by intro x W; simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9, h10, w11, h11]) (a + 2) (by
    intro x W
    have hb := length_bits_le_self W
    simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9, h10, w11, h11] ; nlinarith)
  let c12 := c11.seq r12
  apply c12.withTarget _
  funext x W ip
  apply Turing.Cfg.ext
  · rfl
  · rfl
  · funext j q
    fin_cases j <;> simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9, h10, w11, h11, h12, startupWordsTemplate, startupWords, startupRegisterWords, ← List.replicate_add, Nat.add_comm]
  · funext j
    fin_cases j <;> simp [w0, h0, startupSeedWords, startupSeedHeads, h1, w2, w3, h3, h4, w5, w6, w7, h7, w8, w9, h9, h10, w11, h11, h12, startupWordsTemplate, startupWords, startupRegisterWords, ← List.replicate_add, Nat.add_comm]
  · rfl

/-- The permitted integer row as a startup stage, with its guide width made explicit.

**Proof sketch.** Choose `exists_wordIntTM (-1) a`, strengthen its precondition by recording
the old destination word existentially, and use the published word and scratch readers to
erase the finite control tag. `Contract.ofReaches` packages precisely the chosen row. -/
private theorem startup_integer_stage (a : ℕ) :
    ∃ (T : StartupStage 5 ℕ) (C : ℕ),
      (∀ {x} W (d : Turing.Cfg 5 Bool Unit x), T.pre W d ↔
        (∃ w, WordAt d 2 w ∧ w.length = W + a) ∧ ScratchBlank d) ∧
      (∀ {x} W (d : Turing.Cfg 5 Bool Unit x), T.next W d =
        startupPatch () 2 (bvBits (BitVec.ofInt (W + a) (-1))) d) ∧
      ∀ x W, T.bound x W = C * (W + 1) := by
  obtain ⟨S, hS, hD, M, entry, exit, C, row⟩ := exists_wordIntTM (-1) a
  letI := hS
  letI := hD
  let P := fun {x : List Bool} W (d : Turing.Cfg 5 Bool Unit x) =>
    (∃ w, WordAt d 2 w ∧ w.length = W + a) ∧ ScratchBlank d
  let F := fun {x : List Bool} W (d : Turing.Cfg 5 Bool Unit x) =>
    startupPatch () 2 (bvBits (BitVec.ofInt (W + a) (-1))) d
  have hr : ∀ {x} W (d : Turing.Cfg 5 Bool S x), d.state = some entry →
      P W (startupErase d) → ReachesWithin M d {some exit} (C * (W + 1)) (C * (W + 1))
        (startupAttach exit (F W (startupErase d))) := by
    intro x W d hd hp
    obtain ⟨⟨w, hw, hlen⟩, hs⟩ := hp
    have hs' : ScratchBlank d := by
      rw [scratchBlank_iff] at hs ⊢
      simpa only [startupErase, Cfg.mapState_workTapes] using hs
    have h := row w d hd ((startup_wordAt_erase d 2 w).mp hw) hlen hs'
    change ReachesWithin M d {some exit} (C * (W + 1)) (C * (W + 1))
      (startupAttach exit (startupPatch () 2 (bvBits (BitVec.ofInt (W + a) (-1)))
        (startupErase d)))
    rw [← startupPatch_attach exit 2 (bvBits (BitVec.ofInt (W + a) (-1))) d]
    exact h
  have hx : ∀ {x} W (d : Turing.Cfg 5 Bool S x), d.state = some entry →
      P W (startupErase d) → (startupAttach exit (F W (startupErase d))).state = some exit := by
    intro x W d _ _
    simp only [F, startupPatch, startupAttach, Cfg.mapState_state, Option.map_some]
  refine ⟨StartupStage.ofRow M entry exit P F (fun _ W => C * (W + 1))
    (fun _ W => C * (W + 1)) hr hx, C, fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Embedding a selected word patch patches the corresponding physical tape.

**Proof sketch.** Use the forwarding reconstruction lemma. Selected cells agree by the
word-write equation and injectivity of the bank; outside the bank the destination cannot
occur. The native input, work heads and output are the unchanged frame. -/
private theorem startupEmbed_patch {m K : ℕ} {x : List Bool} (σ : Fin m ↪ Fin K)
    (d : Turing.Cfg K Bool Unit x) (j : Fin m) (w : List Bool) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (startupPatch () j w (d.select σ)) =
      startupPatch () (σ j) w d := by
  rw [Cfg.select_eq]
  apply embedEmitCfg_eq
  · simp only [startupPatch]
  · simp only [startupPatch]
  · simp only [startupPatch, List.append_nil]
  · intro i
    constructor
    · funext q
      simp [startupPatch, wordWrite_apply, σ.injective.eq_iff]
    · simp only [startupPatch]
  · intro a ha
    have hn : a ≠ σ j := fun he => ha ⟨j, he.symm⟩
    constructor
    · funext q
      simp only [startupPatch, wordWrite_apply, hn, false_and, if_false]
    · rfl

/-- The integer row uses the two zero registers as its untouched pair and tapes six/seven
as its blank scratch pair; its destination is the key register. -/
private def startupIntegerBank : Fin 5 ↪ Fin 10 where
  toFun := ![3, 4, 1, 6, 7]
  inj' := by decide

/-- The word bank after installing the signed address of the distinguished initial cell. -/
private def startupKeyWords (a : ℕ) (x : List Bool) (W : ℕ) : Fin 10 → List Bool :=
  Function.update (startupRegisterWords a x W) 1 (keyBits a W (-1))

/-- Install the constant key by the permitted integer row, preserving the entire other bank.

**Proof sketch.** Embed the integer stage in `startupIntegerBank`. The allocated key has
length `W + a` and its two scratch tapes are globally blank. Rewrite the source forecast,
use `startupEmbed_patch`, and identify the same-width replacement with
`startupWords_patch`. Its time coefficient is the integer row's constant. -/
private theorem startup_integer_route (a : ℕ) :
    Nonempty (StartupRoute 10
      (startupWordsTemplate (startupRegisterWords a) (fun _ _ _ => 0))
      (startupWordsTemplate (startupKeyWords a) (fun _ _ _ => 0))) := by
  obtain ⟨T, C, hP, hF, hB⟩ := startup_integer_stage a
  let σ := startupIntegerBank
  refine ⟨StartupRoute.ofStage _ _ (T.embed σ) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_ C ?_⟩
  · intro x W ip
    change T.pre W ((startupWords (startupRegisterWords a x W) (fun _ => 0) ip).select σ)
    rw [hP]
    constructor
    · refine ⟨List.replicate (W + a) false, ?_, by simp⟩
      rw [wordAt_iff]
      intro p _ _
      simp [σ, startupIntegerBank, Cfg.select_eq, startupWords, startupRegisterWords]
    · rw [scratchBlank_iff]
      intro j hj p
      fin_cases j <;> simp_all [σ, startupIntegerBank, Cfg.select_eq, startupWords,
        startupRegisterWords]
  · intro x W ip
    change embedEmitCfg σ _ _ _ (T.next W
      ((startupWords (startupRegisterWords a x W) (fun _ => 0) ip).select σ)) = _
    rw [hF]
    dsimp only [startupWordsTemplate]
    rw [startupEmbed_patch σ (startupWords (startupRegisterWords a x W) (fun _ => 0) ip)]
    have h := startupWords_patch (startupRegisterWords a x W) (fun _ => 0) ip 1
      (bvBits (BitVec.ofInt (W + a) (-1))) rfl
    simpa [σ, startupIntegerBank, startupWordsTemplate, startupKeyWords, keyBits_def,
      startupRegisterWords, bvBits_length] using h
  · intro x W
    change T.bound x W ≤ C * (W + (Nat.bits x.length).length + 1)
    rw [hB]
    nlinarith

/-- Copying the length over a zero register leaves these bits and its unfilled zero suffix. -/
private def startupPaddedLength (W n : ℕ) : List Bool :=
  Nat.bits n ++ List.replicate (W - (Nat.bits n).length) false

/-- Erasing cell `W` delimits the low `W` bits of a padded input length, at every width.

**Proof sketch.** At cell `W` both tapes are blank; negative cells are blank. Inside the
word, `startup_lengthWord` identifies each low bit with the length word's lookup, defaulting
to false. Lookup in `startupPaddedLength` reads that bit before the length word's end, and
reads the padding after it. No condition on the cells beyond the delimiter is needed. -/
private theorem startup_padded_low (W n : ℕ) (p : ℤ) (_hp : -1 ≤ p) (hpW : p ≤ W) :
    Function.update (FinTM.bufferTape (startupPaddedLength W n)) (W : ℤ) none p =
      FinTM.bufferTape (bvBits (wd W n)) p := by
  by_cases he : p = (W : ℤ)
  · subst p
    rw [Function.update_self]
    symm
    apply FinTM.bufferTape_eq_none_of_not_mem
    rw [bvBits_length]
    omega
  rw [Function.update_of_ne he]
  by_cases hp : 0 ≤ p
  · have hp' : p.toNat < W := by omega
    have low : FinTM.bufferTape (bvBits (wd W n)) p =
        some ((Nat.bits n).getD p.toNat false) := by
      rw [startup_lengthWord, FinTM.bufferTape_eq, if_pos hp, List.getElem?_ofFn]
      simp only [dif_pos hp']
    rw [low, startupPaddedLength, FinTM.bufferTape_eq, if_pos hp]
    by_cases hlt : p.toNat < (Nat.bits n).length
    · rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt,
        List.getD_eq_getElem (Nat.bits n) false hlt]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate_of_lt (by omega),
        List.getD_eq_default (Nat.bits n) false (by omega)]
  · rw [FinTM.bufferTape_of_neg _ (by omega), FinTM.bufferTape_of_neg _ (by omega)]

/-- The value tape's trailing delimiter is blank; the unused suffix beyond it is framed. -/
private def startupValueTapes (a : ℕ) (x : List Bool) (W : ℕ) : Fin 10 → ℤ → Option Bool :=
  Function.update (fun j => FinTM.bufferTape (startupKeyWords a x W j)) 2
    (Function.update (FinTM.bufferTape (startupPaddedLength W x.length)) (W : ℤ) none)

/-- All preparation heads return to zero after delimiting the length register. -/
private def startupValueTemplate (a : ℕ) : StartupTemplate 10 :=
  fun {x} W ip => ⟨some (), ip, startupValueTapes a x W, fun _ => 0, []⟩

set_option linter.unusedSimpArgs false in
/-- Form the low-width length word without touching the native input again.

**Proof sketch.** Copy the full length word over the padded zero register. A shared walk
guided by register four moves both heads through `W + 1` cells. The fixed previous-cell leaf
erases the register's cell `W`; shared backward skips then restore both heads. The value
precondition is `startup_padded_low`, so the unused tail can remain beyond the delimiter.
Every call has time linear in `W + |bits |x|| + 1`. -/
private noncomputable def startupValueRoute (a : ℕ) : StartupRoute 10
    (startupWordsTemplate (startupKeyWords a) (fun _ _ _ => 0)) (startupValueTemplate a) := by
  let w0 := startupKeyWords a
  let heads : List Bool → ℕ → Fin 10 → ℤ := fun _ _ _ => 0
  let ws := fun x W => Function.update (w0 x W) (2 : Fin 10)
    (w0 x W 5 ++ (w0 x W 2).drop (w0 x W 5).length)
  let copy := startupCopyRoute w0 heads 5 2 (by decide)
    (by intro x W; rfl) (by intro x W; rfl) 1 (by
      intro x W
      simp [w0, startupKeyWords, startupRegisterWords]
      omega)
  let moved := fun j : Fin 10 => j = 2 ∨ j = 4
  let hw : List Bool → ℕ → Fin 10 → ℤ := fun _ W j => if moved j then ((W + 1 : ℕ) : ℤ) else 0
  let walk : StartupRoute 10 (startupWordsTemplate ws heads) (startupWordsTemplate ws hw) :=
    StartupRoute.ofStage _ _ (startupWalkStage 4 moved (Or.inr rfl) (fun x W => ws x W 4))
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun W ip => startupWords_wordAt _ _ ip 4 rfl)
      (by
        intro x W ip
        change startupWalkPost () moved (ws x W 4) (startupWords (ws x W) (heads x W) ip) = _
        simp [startupWalkPost, startupWordsTemplate, startupWords, heads, hw, ws, w0,
          startupKeyWords, startupRegisterWords])
      1 (by
        intro x W
        change (ws x W 4).length + 1 ≤ 1 * (W + (Nat.bits x.length).length + 1)
        simp [ws, w0, startupKeyWords, startupRegisterWords])
  let cut : StartupTemplate 10 := fun {x} W ip =>
    ⟨some (), ip, startupValueTapes a x W, hw x W, []⟩
  let erase : StartupRoute 10 (startupWordsTemplate ws hw) cut :=
    StartupRoute.ofStage _ _ (startupErasePreviousStage 2) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => trivial)
      (by
        intro x W ip
        change startupErasePreviousPost () 2 (startupWords (ws x W) (hw x W) ip) = _
        apply Turing.Cfg.ext
        · rfl
        · rfl
        · funext j q
          by_cases hj : j = 2
          · subst j
            simp [startupErasePreviousPost, startupWords, cut, startupValueTapes,
              startupPaddedLength, ws, w0, startupKeyWords, startupRegisterWords, hw, moved]
          · simp [startupErasePreviousPost, startupWords, cut, startupValueTapes,
              ws, w0, hj, Function.update_of_ne hj]
        · rfl
        · rfl)
      2 (by intro x W; change 2 ≤ 2 * (W + (Nat.bits x.length).length + 1); omega)
  let hb := fun x W => Function.update (hw x W) (2 : Fin 10) 0
  let back : StartupTemplate 10 := fun {x} W ip =>
    ⟨some (), ip, startupValueTapes a x W, hb x W, []⟩
  let low : List Bool → ℕ → List Bool := fun x W => bvBits (wd W x.length)
  let skip2 : StartupRoute 10 cut back :=
    StartupRoute.ofStage _ _ (startupSkipBackStage 2 low) (fun _ _ => rfl) (fun _ _ => rfl)
      (by
        intro x W ip
        change ∀ p : ℤ, -1 ≤ p → p ≤ ((low x W).length : ℤ) →
          startupValueTapes a x W 2 (hw x W 2 - (low x W).length - 1 + p) =
            FinTM.bufferTape (low x W) p
        intro p hp hpW
        have hi : hw x W 2 - (low x W).length - 1 + p = p := by
          simp [hw, moved, low, bvBits_length]
        rw [hi]
        simpa only [startupValueTapes, Function.update_self, low] using
          startup_padded_low W x.length p hp (by simpa only [low, bvBits_length] using hpW))
      (by
        intro x W ip
        change seekPost () 2 (hw x W 2 - (low x W).length - 1) (cut W ip) = back W ip
        apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
          simp [seekPost_state, seekPost_inputPos, seekPost_workTapes, seekPost_workTapePos,
            seekPost_output, cut, back, hb, hw, moved, low, bvBits_length, Function.update_apply])
      4 (by intro x W; change (low x W).length + 3 ≤ 4 * (W + (Nat.bits x.length).length + 1)
            rw [bvBits_length]; omega)
  let skip4 : StartupRoute 10 back (startupValueTemplate a) :=
    StartupRoute.ofStage _ _ (startupSkipBackStage 4 (fun _ W => List.replicate W false))
      (fun _ _ => rfl) (fun _ _ => rfl)
      (by
        intro x W ip
        change ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate W false).length : ℤ) →
          startupValueTapes a x W 4 (hb x W 4 - (List.replicate W false).length - 1 + p) = _
        intro p _ _
        simp [startupValueTapes, startupKeyWords, startupRegisterWords, hb, hw, moved])
      (by
        intro x W ip
        change seekPost () 4 (hb x W 4 - (List.replicate W false).length - 1) (back W ip) = _
        apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
          simp [seekPost_state, seekPost_inputPos, seekPost_workTapes, seekPost_workTapePos,
            seekPost_output, back, startupValueTemplate, hb, hw, moved, Function.update_apply]
        by_cases h2 : j = 2 <;> by_cases h4 : j = 4 <;> simp_all)
      4 (by intro x W; change (List.replicate W false).length + 3 ≤
              4 * (W + (Nat.bits x.length).length + 1); simp; omega)
  exact (((copy.seq walk).seq erase).seq skip2).seq skip4

/-! ## Private keyed-table installation -/

/-- A single field's layout tape is exactly its finite word buffer. -/
private theorem startup_fields_singleton (w : List Bool) (p : ℤ) :
    fieldsTape [w] p = FinTM.bufferTape w p := by
  by_cases hp : 0 ≤ p
  · rw [fieldsTape_of_nonneg _ hp, joinFields_singleton, FinTM.bufferTape_eq, if_pos hp]
    simp
    cases w[p.toNat]? <;> rfl
  · rw [fieldsTape_of_neg _ (by omega), FinTM.bufferTape_of_neg _ (by omega)]

/-- The empty keyed table occupies just its one-cell header. -/
private theorem startup_keyLength_empty : keyTableLength [] = 1 := by
  simp [keyTableLength_def, keyFields_def, tableFields_eq, joinFields_singleton]

/-- The singleton layout includes two markers and two separators after the header. -/
private theorem startup_keyLength_singleton (k v : List Bool) :
    keyTableLength [(k, v)] = k.length + v.length + 5 := by
  simp [keyTableLength_def, keyFields_def, tableFields_eq, joinFields_cons_cons,
    joinFields_singleton]
  omega

/-- A globally buffered header is the empty keyed table, including both sentinels. -/
private theorem startup_empty_table {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (j : Fin K)
    (hj : d.workTapes j = FinTM.bufferTape [true]) : KeyTableAt d j 0 [] := by
  rw [keyTableAt_iff]
  constructor
  · rw [tableAt_iff, keyFields_def, List.map_nil, tableFields_eq, List.flatten_nil]
    intro p _ _
    rw [zero_add, hj]
    exact (startup_fields_singleton [true] p).symm
  · intro q hq
    rw [startup_keyLength_empty] at hq
    rw [hj]
    exact FinTM.bufferTape_eq_none_of_not_mem [true] (by simp; omega)

/-- Keyed-table assertions depend only on the physical tapes. -/
private theorem startup_keyTable_erase {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (j : Fin K) (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt (startupErase d) j o es ↔ KeyTableAt d j o es := by
  rw [keyTableAt_iff, keyTableAt_iff, tableAt_iff, tableAt_iff]
  simp only [startupErase, Cfg.mapState_workTapes]

/-- The physical forecast of laying out the singleton initial memory. -/
private def startupTablePost {K : ℕ} {S : Type} {x : List Bool} (exit : S) (j : Fin K)
    (es : List (List Bool × List Bool)) (d : Turing.Cfg K Bool S x) : Turing.Cfg K Bool S x :=
  {d with
    state := some exit
    workTapes := keyTableWrite d j (d.workTapePos j) es}

/-- A table write commutes with erasing and reattaching finite control. -/
private theorem startupTable_attach {K : ℕ} {S : Type} {x : List Bool} (exit : S)
    (j : Fin K) (es : List (List Bool × List Bool)) (d : Turing.Cfg K Bool S x) :
    startupTablePost exit j es d = startupAttach exit (startupTablePost () j es (startupErase d)) := by
  rw [startupErase_eq]
  apply Turing.Cfg.ext <;> (try funext a) <;> (try funext q) <;>
    simp only [startupTablePost, startupAttach, keyTableWrite_apply, Cfg.mapState_state,
      Cfg.mapState_inputPos, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      Cfg.mapState_output, Option.map_some]

/-- The permitted keyed-assignment row, specialized to the initial singleton memory.

**Proof sketch.** Choose `exists_keyAssignTM` on the empty table. Read its old layout length
as one, its key length as `W + a`, and its value length as `W`. Its endpoint is the singleton
by `keyAssign_def`. The physical assertion readers remove only the finite control tag.
Package the row with its stated time and radius. -/
private theorem startup_assignment_stage (a : ℕ) :
    ∃ (T : StartupStage 5 ℕ) (C : ℕ),
      (∀ {x} W (d : Turing.Cfg 5 Bool Unit x), T.pre W d ↔
        KeyTableAt d 0 (d.workTapePos 0) [] ∧ WordAt d 1 (keyBits a W (-1)) ∧
        WordAt d 2 (bvBits (wd W x.length)) ∧ ScratchBlank d) ∧
      (∀ {x} W (d : Turing.Cfg 5 Bool Unit x), T.next W d =
        startupTablePost () 0 [(keyBits a W (-1), bvBits (wd W x.length))] d) ∧
      ∀ x W, T.bound x W = C * (2 * W + a + 2) := by
  obtain ⟨S, hS, hD, M, entry, exit, C, row⟩ := exists_keyAssignTM
  letI := hS
  letI := hD
  let P := fun {x : List Bool} W (d : Turing.Cfg 5 Bool Unit x) =>
    KeyTableAt d 0 (d.workTapePos 0) [] ∧ WordAt d 1 (keyBits a W (-1)) ∧
      WordAt d 2 (bvBits (wd W x.length)) ∧ ScratchBlank d
  let F := fun {x : List Bool} W (d : Turing.Cfg 5 Bool Unit x) =>
    startupTablePost () 0 [(keyBits a W (-1), bvBits (wd W x.length))] d
  have hr : ∀ {x} W (d : Turing.Cfg 5 Bool S x), d.state = some entry →
      P W (startupErase d) → ReachesWithin M d {some exit} (C * (2 * W + a + 2))
        (C * (2 * W + a + 2)) (startupAttach exit (F W (startupErase d))) := by
    intro x W d hd hp
    obtain ⟨htable, hkey, hval, hs⟩ := hp
    rw [startupErase, Cfg.mapState_workTapePos] at htable
    have htable' : KeyTableAt d 0 (d.workTapePos 0) [] :=
      (startup_keyTable_erase d 0 _ []).mp htable
    have hs' : ScratchBlank d := by
      rw [scratchBlank_iff] at hs ⊢
      simpa only [startupErase, Cfg.mapState_workTapes] using hs
    have h := row (d.workTapePos 0) [] (keyBits a W (-1)) (bvBits (wd W x.length)) d hd rfl
      htable' ((startup_wordAt_erase d 1 _).mp hkey) ((startup_wordAt_erase d 2 _).mp hval)
      (by simp) hs'
    have hlen : keyTableLength [] + (keyBits a W (-1)).length +
        (bvBits (wd W x.length)).length + 1 = 2 * W + a + 2 := by
      rw [startup_keyLength_empty, keyBits_def, bvBits_length, bvBits_length]
      omega
    rw [hlen] at h
    have hnil : keyAssign [] (keyBits a W (-1)) (bvBits (wd W x.length)) =
        [(keyBits a W (-1), bvBits (wd W x.length))] := by simp [keyAssign_def]
    rw [hnil] at h
    change ReachesWithin M d {some exit} _ _ (startupAttach exit
      (startupTablePost () 0 [(keyBits a W (-1), bvBits (wd W x.length))] (startupErase d)))
    rw [← startupTable_attach exit 0 _ d]
    exact h
  have hx : ∀ {x} W (d : Turing.Cfg 5 Bool S x), d.state = some entry →
      P W (startupErase d) → (startupAttach exit (F W (startupErase d))).state = some exit := by
    intro x W d _ _
    simp only [F, startupTablePost, startupAttach, Cfg.mapState_state, Option.map_some]
  exact ⟨StartupStage.ofRow M entry exit P F (fun _ W => C * (2 * W + a + 2))
    (fun _ W => C * (2 * W + a + 2)) hr hx, C, fun _ _ => Iff.rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- Embedding a table write writes the corresponding host tape at the same origin.

**Proof sketch.** Reconstruct the forwarding embedding, using `keyTableWrite_apply` and
bank injectivity on selected tapes. Every unselected tape is the original frame, since it
cannot be the selected table destination. -/
private theorem startupEmbed_table {m K : ℕ} {x : List Bool} (σ : Fin m ↪ Fin K)
    (d : Turing.Cfg K Bool Unit x) (j : Fin m) (es : List (List Bool × List Bool)) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (startupTablePost () j es (d.select σ)) =
      startupTablePost () (σ j) es d := by
  rw [Cfg.select_eq]
  apply embedEmitCfg_eq
  · simp only [startupTablePost]
  · simp only [startupTablePost]
  · simp only [startupTablePost, List.append_nil]
  · intro i
    constructor
    · funext q
      simp [startupTablePost, keyTableWrite_apply, σ.injective.eq_iff]
    · rfl
  · intro a ha
    have hn : a ≠ σ j := fun he => ha ⟨j, he.symm⟩
    constructor
    · funext q
      simp only [startupTablePost, keyTableWrite_apply, hn, false_and, if_false]
    · rfl

/-- Select the table, key, value and two globally blank scratch tapes for keyed assignment. -/
private def startupAssignmentBank : Fin 5 ↪ Fin 10 where
  toFun := ![0, 1, 2, 6, 7]
  inj' := by decide

/-- The final preparation template contains the installed initial-memory singleton. -/
private def startupFinishedTemplate (a : ℕ) : StartupTemplate 10 := fun {x} W ip =>
  startupTablePost () 0 [(keyBits a W (-1), bvBits (wd W x.length))]
    (startupValueTemplate a W ip)

/-- Install the singleton memory table through the permitted keyed-assignment row.

**Proof sketch.** The source bank sees the buffered empty header, the prepared key and the
delimited low-width length value. The two scratch tapes are globally blank. Rewrite the
source forecast and use `startupEmbed_table` for the framed physical endpoint. -/
private theorem startup_assignment_route (a : ℕ) : Nonempty (StartupRoute 10
    (startupValueTemplate a) (startupFinishedTemplate a)) := by
  obtain ⟨T, C, hP, hF, hB⟩ := startup_assignment_stage a
  let σ := startupAssignmentBank
  refine ⟨StartupRoute.ofStage _ _ (T.embed σ) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
    (C * (a + 4)) ?_⟩
  · intro x W ip
    change T.pre W ((startupValueTemplate a W ip).select σ)
    rw [hP]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hi : ((startupValueTemplate a W ip).select σ).workTapePos 0 = 0 := by
        rw [Cfg.select_eq]
        rfl
      rw [hi]
      apply startup_empty_table
      simp [σ, startupAssignmentBank, Cfg.select_eq, startupValueTemplate, startupValueTapes,
        startupKeyWords, startupRegisterWords]
    · rw [wordAt_iff]
      intro p _ _
      simp [σ, startupAssignmentBank, Cfg.select_eq, startupValueTemplate, startupValueTapes,
        startupKeyWords]
    · rw [wordAt_iff]
      intro p hp hpW
      simpa [σ, startupAssignmentBank, Cfg.select_eq, startupValueTemplate, startupValueTapes,
        bvBits_length] using startup_padded_low W x.length p hp (by simpa only [bvBits_length] using hpW)
    · rw [scratchBlank_iff]
      intro j hj p
      fin_cases j <;> simp_all [σ, startupAssignmentBank, Cfg.select_eq, startupValueTemplate,
        startupValueTapes, startupKeyWords, startupRegisterWords]
  · intro x W ip
    change embedEmitCfg σ (startupValueTemplate a W ip).workTapes
      (startupValueTemplate a W ip).workTapePos (startupValueTemplate a W ip).output
      (T.next W ((startupValueTemplate a W ip).select σ)) = _
    rw [hF, startupEmbed_table]
    rfl
  · intro x W
    change T.bound x W ≤ C * (a + 4) * (W + (Nat.bits x.length).length + 1)
    rw [hB]
    calc
      _ ≤ C * ((a + 4) * (W + (Nat.bits x.length).length + 1)) := by
        apply Nat.mul_le_mul_left
        nlinarith
      _ = _ := by ring

/-- Writing the singleton over a buffered empty header gives its complete keyed-table layout.

**Proof sketch.** Inside the new layout use `keyTableWrite_apply`. Outside, the old header
is blank: on negative cells by the buffer reader, and past the layout because the singleton
layout has length at least one. These cases give both sentinels and every trailing cell. -/
private theorem startup_table_post_at {K : ℕ} {S : Type} {x : List Bool}
    (exit : S) (d : Turing.Cfg K Bool S x) (j : Fin K) (k v : List Bool)
    (hp : d.workTapePos j = 0) (ht : d.workTapes j = FinTM.bufferTape [true]) :
    KeyTableAt (startupTablePost exit j [(k, v)] d) j 0 [(k, v)] := by
  have hL : 1 ≤ keyTableLength [(k, v)] := by rw [startup_keyLength_singleton]; omega
  rw [keyTableAt_iff]
  constructor
  · rw [tableAt_iff]
    intro p _ _
    change keyTableWrite d j (d.workTapePos j) [(k, v)] j (0 + p) = _
    rw [hp, zero_add, keyTableWrite_apply]
    by_cases hi : 0 ≤ p ∧ p < (keyTableLength [(k, v)] : ℤ)
    · rw [if_pos ⟨rfl, hi.1, by simpa only [zero_add] using hi.2⟩, sub_zero]
    · rw [if_neg (by simpa only [true_and, zero_add] using hi), ht]
      by_cases hn : p < 0
      · rw [FinTM.bufferTape_of_neg _ hn, fieldsTape_of_neg _ hn]
      · have he : (keyTableLength [(k, v)] : ℤ) ≤ p := by omega
        rw [FinTM.bufferTape_eq_none_of_not_mem [true] (by simp; omega)]
        symm
        apply fieldsTape_of_length_le
        simpa only [keyTableLength_def] using he
  · intro q hq
    change keyTableWrite d j (d.workTapePos j) [(k, v)] j q = none
    rw [hp, keyTableWrite_apply, if_neg (by omega), ht]
    exact FinTM.bufferTape_eq_none_of_not_mem [true] (by simp; omega)

set_option linter.unusedSimpArgs false in
/-- The finished ten-tape template encodes the initial RAM configuration on its first eight.

**Proof sketch.** Apply `startup_encodes_of_tapes`. The singleton layout is
`startup_table_post_at`; all other tapes are the frame of that write. The key and zero
registers have their allocated lengths, register two is `startup_padded_low`, and tape five
is the full binary input length. Both scratch tapes are blank and every head is zero. -/
private theorem startup_finished_encodes (a : ℕ) (ha : 1 ≤ a) (fn : Bool)
    {x : List Bool} (W : ℕ) (ip : Fin (x.length + 2)) :
    Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb 2) (fun _ => 0)
      (startupFinishedTemplate a W ip) := by
  apply startup_encodes_of_tapes a fn (Fin.castAddEmb 2) (fun _ => 0)
  · exact startup_inRange_neg_one (W + a) (by omega)
  · intro j; rfl
  · apply startup_table_post_at () (startupValueTemplate a W ip) 0 _ _ rfl
    funext q
    simp [startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
  · refine ⟨keyBits a W (-1), ?_, ?_⟩
    · show WordAt (startupFinishedTemplate a W ip) (1 : Fin 10) (keyBits a W (-1))
      rw [wordAt_iff]
      intro p _ _
      simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes, startupKeyWords]
    · rw [keyBits_def, bvBits_length]
  · intro r hr₂ hr₄
    have h : r = 2 ∨ r = 3 ∨ r = 4 := by fin_cases r <;> simp_all
    rcases h with rfl | rfl | rfl
    · refine ⟨bvBits (wd W x.length), ?_, bvBits_length _⟩
      show WordAt (startupFinishedTemplate a W ip) (2 : Fin 10) (bvBits (wd W x.length))
      rw [wordAt_iff]
      intro p hp hpW
      simpa [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes] using
        startup_padded_low W x.length p hp (by simpa only [bvBits_length] using hpW)
    · refine ⟨List.replicate W false, ?_, List.length_replicate ..⟩
      show WordAt (startupFinishedTemplate a W ip) (3 : Fin 10) (List.replicate W false)
      rw [wordAt_iff]
      intro p _ _
      simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
    · refine ⟨List.replicate W false, ?_, List.length_replicate ..⟩
      show WordAt (startupFinishedTemplate a W ip) (4 : Fin 10) (List.replicate W false)
      rw [wordAt_iff]
      intro p _ _
      simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
  · show WordAt (startupFinishedTemplate a W ip) (5 : Fin 10) (Nat.bits x.length)
    rw [wordAt_iff]
    intro p _ _
    simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
      startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
  · intro r hr q
    have h : r = 6 ∨ r = 7 := by fin_cases r <;> simp_all
    rcases h with rfl | rfl
    · show (startupFinishedTemplate a W ip).workTapes (6 : Fin 10) q = none
      simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
    · show (startupFinishedTemplate a W ip).workTapes (7 : Fin 10) q = none
      simp [startupFinishedTemplate, startupTablePost, keyTableWrite_apply,
        startupValueTemplate, startupValueTapes, startupKeyWords, startupRegisterWords]
  · rfl

/-- Compose the ordinary preparation after input counting; its route has a uniform linear
time coefficient and therefore a linear work radius. -/
private theorem startup_preparation_route (a : ℕ) : Nonempty (StartupRoute 10
    (startupWordsTemplate startupSeedWords startupSeedHeads) (startupFinishedTemplate a)) := by
  obtain ⟨key⟩ := startup_integer_route a
  obtain ⟨table⟩ := startup_assignment_route a
  exact ⟨(((startupRegisterRoute a).seq key).seq (startupValueRoute a)).seq table⟩

/-! ## Private native counting composition -/

/-- First advance off the native left boundary, then use the shared input rewind. -/
private noncomputable def startupPositionStage (K : ℕ) : StartupStage K ℕ :=
  (startupAdvanceInputStage K).seq (startupInputRewindStage K) id (by
    intro x W d _
    change 1 ≤ (moveInputPos d.inputPos .pos).val
    exact startup_advance_positive d.inputPos)

/-- The native positioning composition keeps all work data and ends at input position one. -/
private theorem startupPosition_next (K : ℕ) {x : List Bool} (W : ℕ)
    (d : Turing.Cfg K Bool Unit x) :
    (startupPositionStage K).next W d = startupInputPost () 1 d := by
  apply Turing.Cfg.ext <;> rfl

/-- Native positioning has zero work radius, including its stationary dispatch. -/
private theorem startupPosition_radius (K : ℕ) :
    (startupPositionStage K).Radius (fun _ _ => 0) := by
  obtain ⟨ha, hr⟩ := startup_native_position_radius K
  intro x W d hd hp u hu j
  have h := StartupStage.radius_seq (startupAdvanceInputStage K)
    (startupInputRewindStage K) id (by
      intro x W d _
      change 1 ≤ (moveInputPos d.inputPos .pos).val
      exact startup_advance_positive d.inputPos) (fun _ _ => 0) (fun _ _ => 0)
    @ha @hr (x := x) W d hd hp u hu j
  simpa only [zero_add, Nat.cast_zero] using h

/-- Compose native positioning with the length row in any blank selected bank.

**Proof sketch.** Strengthen positioning to the blank-bank precondition, retaining its
original contract time and radius. Its physical forecast is the input-only update to one,
so the length row's precondition follows. Compose through the shared seam. Its forecast is
`startupEmbed_patch`; its radius is the sum of zero and the length row's logarithmic radius.
The two positioning runs and dispatches are absorbed by six times `|x| + 1`. -/
private theorem startup_native_stage {m K : ℕ} (σ : Fin (m + 1) ↪ Fin K)
    (L : StartupStage (m + 1) ℕ) (C : ℕ)
    (hP : ∀ {x} W (d : Turing.Cfg (m + 1) Bool Unit x),
      L.pre W d ↔ d.inputPos = 1 ∧ ∀ j q, d.workTapes j q = none)
    (hF : ∀ {x} W (d : Turing.Cfg (m + 1) Bool Unit x),
      L.next W d = startupPatch () 0 (Nat.bits x.length) d)
    (hB : ∀ x W, L.bound x W = C * (x.length + 1))
    (hE : L.Radius (fun x _ => C * ((Nat.bits x.length).length + 1))) :
    ∃ N : StartupStage K ℕ,
      (∀ {x} W (d : Turing.Cfg K Bool Unit x),
        N.pre W d ↔ ∀ j q, d.workTapes (σ j) q = none) ∧
      (∀ {x} W (d : Turing.Cfg K Bool Unit x), N.next W d =
        startupPatch () (σ 0) (Nat.bits x.length) (startupInputPost () 1 d)) ∧
      (∀ x W, N.bound x W ≤ (C + 6) * (x.length + 1)) ∧
      N.Radius (fun x _ => C * ((Nat.bits x.length).length + 1)) := by
  let P := fun {x : List Bool} (_ : ℕ) (d : Turing.Cfg K Bool Unit x) =>
    ∀ j q, d.workTapes (σ j) q = none
  let pos := startupPositionStage K
  have accepts : ∀ {x} W (d : Turing.Cfg K Bool Unit x), P W d → pos.pre W d := by
    intro x W d _
    trivial
  let Q := pos.spec P pos.next accepts (fun _ _ _ => rfl)
  let T := L.embed σ
  have link : ∀ {x} W (d : Turing.Cfg K Bool Unit x), Q.pre W d → T.pre W (Q.next W d) := by
    intro x W d hp
    change L.pre W ((pos.next W d).select σ)
    rw [startupPosition_next, hP]
    constructor
    · simp only [Cfg.select_eq, startupInputPost]
    · intro j q
      simpa only [Cfg.select_eq, startupInputPost] using hp j q
  let N := Q.seq T id link
  refine ⟨N, fun _ _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro x W d
    change embedEmitCfg σ (pos.next W d).workTapes (pos.next W d).workTapePos
      (pos.next W d).output (L.next W ((pos.next W d).select σ)) = _
    rw [startupPosition_next, hF, startupEmbed_patch]
  · intro x W
    change (startupPositionStage K).bound x W + 1 + L.bound x W ≤ (C + 6) * (x.length + 1)
    rw [hB]
    change (1 + 1 + (x.length + 2)) + 1 + C * (x.length + 1) ≤ (C + 6) * (x.length + 1)
    nlinarith
  · have hQ : Q.Radius (fun _ _ => 0) := by
      intro x W d hd hp u hu j
      exact startupPosition_radius K W d hd (accepts W _ hp) u hu j
    have hT : T.Radius (fun x _ => C * ((Nat.bits x.length).length + 1)) := by
      intro x W d hd hp u hu j
      exact StartupStage.radius_embed σ L _ @hE (x := x) W d hd hp u hu j
    intro x W d hd hp u hu j
    have h := StartupStage.radius_seq Q T id @link
      (fun _ _ => 0) (fun x _ => C * ((Nat.bits x.length).length + 1)) @hQ @hT
      (x := x) W d hd hp u hu j
    simpa only [zero_add] using h

/-! ## Private placement beside the width witness -/

/-- Eight simulation tapes, the witness bank, capture/counter tapes and length scratch bank. -/
private abbrev startupTapeCount (m l : ℕ) := 8 + (m + (l + 2))

/-- Place the preparation's first eight tapes first, then its width master and counter. -/
private def startupOrdinaryBank (m l : ℕ) : Fin 10 ↪ Fin (startupTapeCount m l) where
  toFun j := if h : j.val < 8 then ⟨j.val, by change j.val < 8 + (m + (l + 2)); omega⟩
    else ⟨8 + m + (j.val - 8), by
      change 8 + m + (j.val - 8) < 8 + (m + (l + 2))
      have := j.isLt
      omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> omega

/-- The length row's output is tape five; its private tapes follow capture and counter. -/
private def startupLengthBank (m l : ℕ) : Fin (l + 1) ↪ Fin (startupTapeCount m l) where
  toFun j := if h : j.val = 0 then ⟨5, by change 5 < 8 + (m + (l + 2)); omega⟩
    else ⟨8 + m + 1 + j.val, by
      change 8 + m + 1 + j.val < 8 + (m + (l + 2))
      have := j.isLt
      omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> omega

/-- The preparation master is the returning silent embedding's capture tape. -/
private theorem startupOrdinary_capture (m l : ℕ) :
    startupOrdinaryBank m l 8 = startupCaptureIndex m (l + 1) := by
  apply Fin.ext
  simp [startupOrdinaryBank, startupCaptureIndex]

/-- Native counting and ordinary preparation use the same physical length tape. -/
private theorem startupLength_zero (m l : ℕ) :
    startupLengthBank m l 0 = startupOrdinaryBank m l 5 := by
  apply Fin.ext
  simp [startupLengthBank, startupOrdinaryBank]

/-- The preparation preserves the required ordering of the eight simulation tapes. -/
private theorem startupOrdinary_first (m l : ℕ) :
    (Fin.castAddEmb 2).trans (startupOrdinaryBank m l) = Fin.castAddEmb (m + (l + 2)) := by
  apply Function.Embedding.ext
  intro j
  apply Fin.ext
  show (startupOrdinaryBank m l (⟨j.val, by have := j.isLt; omega⟩ : Fin 10)).val = j.val
  simp [startupOrdinaryBank, j.isLt]

/-- Every preparation tape lies outside the width witness's selected bank. -/
private theorem startupOrdinary_fresh (m l : ℕ) (j : Fin 10) :
    startupOrdinaryBank m l j ∉ Set.range (startupBank m (l + 1)) := by
  rintro ⟨i, he⟩
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  have hb : (startupBank m (l + 1) i).val = 8 + i.val := rfl
  rw [hb] at hv
  simp only [startupOrdinaryBank, Function.Embedding.coeFn_mk] at hv
  split_ifs at hv <;> dsimp only at hv <;> omega

/-- The length bank is outside the witness bank and avoids the capture tape. -/
private theorem startupLength_fresh (m l : ℕ) (j : Fin (l + 1)) :
    startupLengthBank m l j ∉ Set.range (startupBank m (l + 1)) ∧
      startupLengthBank m l j ≠ startupCaptureIndex m (l + 1) := by
  constructor
  · rintro ⟨i, he⟩
    have hv := congrArg Fin.val he
    have hi := i.isLt
    have hb : (startupBank m (l + 1) i).val = 8 + i.val := rfl
    rw [hb] at hv
    simp only [startupLengthBank, Function.Embedding.coeFn_mk] at hv
    split_ifs at hv <;> dsimp only at hv <;> omega
  · intro he
    have hv := congrArg Fin.val he
    have hc : (startupCaptureIndex m (l + 1)).val = 8 + m := by
      change 8 + (m + 0) = 8 + m
      omega
    rw [hc] at hv
    simp only [startupLengthBank, Function.Embedding.coeFn_mk] at hv
    split_ifs at hv <;> dsimp only at hv <;> omega

/-- The exact physical facts supplied by silent capture, with the finite control erased. -/
private def startupReady (m l W : ℕ) {x : List Bool}
    (d : Turing.Cfg (startupTapeCount m l) Bool Unit x) : Prop :=
  d.state = some () ∧ d.output = [] ∧
  d.workTapes (startupCaptureIndex m (l + 1)) = FinTM.bufferTape (Nat.bits W) ∧
  d.workTapePos (startupCaptureIndex m (l + 1)) = ((Nat.bits W).length : ℤ) ∧
  ∀ j, j ∉ Set.range (startupBank m (l + 1)) → j ≠ startupCaptureIndex m (l + 1) →
    d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0

/-- The capture frame makes every preparation tape other than the master globally blank. -/
private theorem startupReady_ordinary {m l W : ℕ} {x : List Bool}
    (d : Turing.Cfg (startupTapeCount m l) Bool Unit x) (h : startupReady m l W d)
    (j : Fin 10) (hj : j ≠ 8) :
    d.workTapes (startupOrdinaryBank m l j) = (fun _ => none) ∧
      d.workTapePos (startupOrdinaryBank m l j) = 0 := by
  apply h.2.2.2.2 _ (startupOrdinary_fresh m l j)
  rw [← startupOrdinary_capture]
  exact (startupOrdinaryBank m l).injective.ne hj

/-- Counting supplies precisely the canonical start expected by ordinary preparation.

**Proof sketch.** Select the ordinary bank after the input-only rewind and length patch.
The master is the capture tape; every other selected tape was globally blank by the capture
frame. The length patch therefore turns exactly tape five into its finite binary buffer.
The selected head vector is the captured width's ending head and zero everywhere else. -/
private theorem startup_seed_after_length {m l W : ℕ} {x : List Bool}
    (d : Turing.Cfg (startupTapeCount m l) Bool Unit x) (h : startupReady m l W d) :
    (startupPatch () (startupLengthBank m l 0) (Nat.bits x.length)
      (startupInputPost () 1 d)).select (startupOrdinaryBank m l) =
      startupWordsTemplate startupSeedWords startupSeedHeads W (1 : Fin (x.length + 2)) := by
  let σ := startupOrdinaryBank m l
  have ht (j : Fin 10) : d.workTapes (σ j) =
      if j = 8 then FinTM.bufferTape (Nat.bits W) else (fun _ => none) := by
    by_cases hj : j = 8
    · subst j
      simpa only [σ, startupOrdinary_capture, if_pos rfl] using h.2.2.1
    · simpa only [if_neg hj] using (startupReady_ordinary d h j hj).1
  have hp (j : Fin 10) : d.workTapePos (σ j) =
      if j = 8 then ((Nat.bits W).length : ℤ) else 0 := by
    by_cases hj : j = 8
    · subst j
      simpa only [σ, startupOrdinary_capture, if_pos rfl] using h.2.2.2.1
    · simpa only [if_neg hj] using (startupReady_ordinary d h j hj).2
  rw [startupLength_zero, Cfg.select_eq]
  apply Turing.Cfg.ext
  · rfl
  · rfl
  · funext j q
    change wordWrite (startupInputPost () 1 d) (σ 5) (Nat.bits x.length) (σ j) q = _
    rw [wordWrite_apply]
    simp only [startupInputPost, σ.injective.eq_iff, ht, hp]
    fin_cases j <;> simp [startupWordsTemplate, startupWords, startupSeedWords]
    intro hq
    symm
    apply FinTM.bufferTape_eq_none_of_not_mem
    rintro ⟨h₀, h₁⟩
    exact not_lt_of_ge (hq h₀) h₁
  · funext j
    change d.workTapePos (σ j) = _
    rw [hp]
    fin_cases j <;> simp [startupWordsTemplate, startupWords, startupSeedHeads]
  · rfl

/-- The initial-configuration encoding is invariant under finite-control relabeling. -/
private theorem startup_encodes_mapState {K : ℕ} {S T : Type} {x : List Bool}
    (a W : ℕ) (fn : Bool) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (f : S → T) :
    Encodes a fn {-1} (XCfg.init W x.length) σ o (d.mapState f) ↔
      Encodes a fn {-1} (XCfg.init W x.length) σ o d := by
  rw [encodes_iff, encodes_iff]
  simp only [wordAt_iff, keyTableAt_iff, tableAt_iff, Cfg.mapState_workTapes,
    Cfg.mapState_workTapePos, Cfg.mapState_output]

/-- Forwarding the prepared bank into an empty-output frame preserves its RAM encoding.

**Proof sketch.** Read the encoding and its tape predicates through their published
equivalences. Each selected tape and head is the source tape or head by the forwarding
embedding's selected-bank readers, and its physical output has the empty prefix. -/
private theorem startup_encodes_embed {K : ℕ} {S : Type} {x : List Bool}
    (a W : ℕ) (fn : Bool) (τ : Fin 10 ↪ Fin K) (tapes : Fin K → ℤ → Option Bool)
    (heads : Fin K → ℤ) (d : Turing.Cfg 10 Bool S x)
    (h : Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb 2) (fun _ => 0) d) :
    Encodes a fn {-1} (XCfg.init W x.length) ((Fin.castAddEmb 2).trans τ) (fun _ => 0)
      (embedEmitCfg τ tapes heads [] d) := by
  rw [encodes_iff] at h ⊢
  simp only [wordAt_iff, keyTableAt_iff, tableAt_iff, Function.Embedding.coe_trans,
    Function.comp_apply, embedEmitCfg_selected_tape, embedEmitCfg_selected_pos,
    embedEmitCfg_output, List.nil_append] at h ⊢
  exact h

/-- All work after silent capture: native counting followed by the prepared RAM bank.

**Proof sketch.** Choose the length row and the ten-tape preparation route. Embed counting
in its fresh bank, strengthen its precondition to the capture facts, and compose with the
embedded preparation. `startup_seed_after_length` verifies the exact physical seam. The
prepared endpoint encodes the initial RAM by the selected-bank embedding lemma. For time,
use `|bits n| ≤ n` and `W ≤ W²`; for space, add the counting radius and the preparation's
time-derived radius, without including the width witness in either. -/
private theorem startup_after_capture (a : ℕ) (ha : 1 ≤ a) (fn : Bool) (m : ℕ) :
    ∃ (l : ℕ) (P : StartupStage (startupTapeCount m l) ℕ) (Ct Ce : ℕ),
      (∀ {x} W (d : Turing.Cfg (startupTapeCount m l) Bool Unit x),
        P.pre W d ↔ startupReady m l W d) ∧
      (∀ {x} W (d : Turing.Cfg (startupTapeCount m l) Bool Unit x), P.pre W d →
        Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb (m + (l + 2))) (fun _ => 0)
          (P.next W d)) ∧
      (∀ x W, P.bound x W ≤ Ct * (x.length + W ^ 2 + 1)) ∧
      P.Radius (fun x W => Ce * (W + (Nat.bits x.length).length + 1)) := by
  obtain ⟨l, L, C, hLP, hLF, hLB, hLE⟩ := startup_length_stage
  obtain ⟨O⟩ := startup_preparation_route a
  obtain ⟨N, hNP, hNF, hNB, hNE⟩ := startup_native_stage (startupLengthBank m l) L C
    @hLP @hLF hLB @hLE
  have accepts : ∀ {x} W (d : Turing.Cfg (startupTapeCount m l) Bool Unit x),
      startupReady m l W d → N.pre W d := by
    intro x W d hp
    rw [hNP]
    intro j q
    exact congrFun (hp.2.2.2.2 _ (startupLength_fresh m l j).1
      (startupLength_fresh m l j).2).1 q
  let Q := N.spec (fun W d => startupReady m l W d) N.next accepts (fun _ _ _ => rfl)
  let R := O.stage.embed (startupOrdinaryBank m l)
  have link : ∀ {x} W (d : Turing.Cfg (startupTapeCount m l) Bool Unit x),
      Q.pre W d → R.pre W (Q.next W d) := by
    intro x W d hp
    change O.stage.pre W ((N.next W d).select (startupOrdinaryBank m l))
    rw [O.pre_eq, hNF, startup_seed_after_length d hp]
    rfl
  let P := Q.seq R id link
  refine ⟨l, P, (C + 6) + O.coefficient + 1, C + O.coefficient,
    fun _ _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro x W d hp
    change Encodes a fn {-1} (XCfg.init W x.length) _ (fun _ => 0)
      (embedEmitCfg (startupOrdinaryBank m l) (N.next W d).workTapes
        (N.next W d).workTapePos (N.next W d).output
        (O.stage.next W ((N.next W d).select (startupOrdinaryBank m l))))
    rw [O.next_eq]
    have hout : (N.next W d).output = [] := by
      rw [hNF]
      exact hp.2.1
    rw [hout, ← startupOrdinary_first m l]
    apply startup_encodes_embed
    exact startup_finished_encodes a ha fn W _
  · intro x W
    let U := x.length + W ^ 2 + 1
    have hW : W ≤ W ^ 2 := by
      by_cases h : W = 0
      · subst W; simp
      · have : 1 ≤ W := by omega
        nlinarith
    have hn : x.length + 1 ≤ U := by dsimp only [U]; omega
    have hv : W + (Nat.bits x.length).length + 1 ≤ U := by
      have hb := length_bits_le_self x.length
      dsimp only [U]
      omega
    have hn' := (hNB x W).trans (Nat.mul_le_mul_left (C + 6) hn)
    have ho' := (O.bound_le x W).trans (Nat.mul_le_mul_left O.coefficient hv)
    change N.bound x W + 1 + O.stage.bound x W ≤ ((C + 6) + O.coefficient + 1) * U
    calc
      _ ≤ (C + 6) * U + 1 + O.coefficient * U :=
        Nat.add_le_add (Nat.add_le_add_right hn' 1) ho'
      _ = ((C + 6) + O.coefficient) * U + 1 := by ring
      _ ≤ ((C + 6) + O.coefficient + 1) * U := by
        conv_rhs => rw [Nat.add_mul, one_mul]
        exact Nat.add_le_add_left (by dsimp only [U]; omega : 1 ≤ U) _
  · have hQ : Q.Radius (fun x _ => C * ((Nat.bits x.length).length + 1)) := by
      intro x W d hd hp u hu j
      exact hNE W d hd (accepts W _ hp) u hu j
    have hO : O.stage.Radius O.stage.bound := by
      intro x W d hd hp u hu j
      exact StartupStage.radius_time O.stage (x := x) W d hd hp u hu j
    have hR : R.Radius O.stage.bound := by
      intro x W d hd hp u hu j
      exact StartupStage.radius_embed (startupOrdinaryBank m l) O.stage _ @hO
        (x := x) W d hd hp u hu j
    intro x W d hd hp u hu j
    have h := StartupStage.radius_seq Q R id @link
      (fun x _ => C * ((Nat.bits x.length).length + 1)) O.stage.bound @hQ @hR
      (x := x) W d hd hp u hu j
    have hb : C * ((Nat.bits x.length).length + 1) + O.stage.bound x W ≤
        (C + O.coefficient) * (W + (Nat.bits x.length).length + 1) := by
      calc
        _ ≤ C * ((Nat.bits x.length).length + 1) +
            O.coefficient * (W + (Nat.bits x.length).length + 1) := Nat.add_le_add_left (O.bound_le x W) _
        _ ≤ C * (W + (Nat.bits x.length).length + 1) +
            O.coefficient * (W + (Nat.bits x.length).length + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) _
        _ = _ := by ring
    exact h.trans (by exact_mod_cast hb)

/-- Initial blank configurations commute with finite-control relabeling. -/
private theorem startup_init_mapState {K : ℕ} {S T : Type} (entry : S) (f : S → T)
    (x : List Bool) : (Turing.Cfg.init (k := K) entry x).mapState f = Turing.Cfg.init (f entry) x := by
  apply Turing.Cfg.ext <;> (try funext j) <;> (try funext q) <;>
    simp only [Cfg.mapState_state, Cfg.mapState_inputPos, Cfg.mapState_workTapes,
      Cfg.mapState_workTapePos, Cfg.mapState_output, Cfg.init_state, Cfg.init_inputPos,
      Cfg.init_workTapes, Cfg.init_workTapePos, Cfg.init_output, Option.map_some]

/-- A radius proportional to a positive size has a visited-cell bound of the same size. -/
private theorem startup_space_factor (K E V : ℕ) (hV : 1 ≤ V) :
    K * (2 * (E * V) + 1) ≤ (K * (2 * E + 1)) * V := by
  calc
    _ ≤ K * ((2 * E) * V + V) := Nat.mul_le_mul_left K (by nlinarith)
    _ = _ := by ring

/-- **The start-up.** For `a ≥ 1`, an output mode `fn` and a word-size witness `Mw`, there is a
machine with the eight tapes of `WordRAM.Sim.Encodes` first and `k'` more, and a constant `C`, such
that: whenever `Mw`, run on `x`, writes `Nat.bits W` within `tw` steps having visited at most `sw`
work cells, the machine, started at its entry on `x` with blank tapes, reaches its exit at some
time `t ≤ tw + C·(|x| + W² + 1)`, not earlier, in a configuration whose first eight tapes encode
`XCfg.init W |x|` over the cells `{-1}` with some origins, having visited at most
`sw + C·(W + log |x| + 1)` work cells. [AB09, Exercise 1.9]

**Proof sketch.** Run `Mw` through `embedSilentRetTM`, capturing `Nat.bits W` and retaining
its coefficient-one space bound. Advance and rewind the native input head, then use
`exists_inputLengthTM` in a disjoint blank bank; its logarithmic work radius is retained by
contract composition. The ordinary preparation rewinds the width master, reuses a copied
counter for `expandTM`, copies the zero registers, and extends the key with a fixed advancing
writer. The permitted integer row writes the key of `-1`. Copy the length over its padded
register, walk to offset `W + 1`, erase its preceding cell, and use backward skips to delimit
and restore the low-width value. The permitted keyed assignment installs the singleton table.
`startup_finished_encodes` supplies the initial RAM encoding, including `W = 0, a = 1`.
Compose capture and preparation with the shared seam's run, first-return and visited-space
sum theorems. The preparation's radius is linear in `W + |Nat.bits |x|| + 1`, and its time
is bounded by a constant times `|x| + W² + 1`. -/
theorem exists_startup (a : ℕ) (ha : 1 ≤ a) (fn : Bool) (Mw : FinTM Bool) :
    ∃ (k' : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (8 + k') Bool S) (entry exit : S) (C : ℕ),
      ∀ (x : List Bool) (W tw sw : ℕ), Mw.ComputesInTime x (Nat.bits W) tw →
        Mw.tm.spaceUsed (Mw.tm.initCfg x) tw ≤ sw →
        ∃ (t : ℕ) (o : Fin 8 → ℤ), t ≤ tw + C * (x.length + W ^ 2 + 1) ∧
          (∀ s < t, (R.runFrom (Turing.Cfg.init entry x) s).state ≠ some exit) ∧
          (R.runFrom (Turing.Cfg.init entry x) t).state = some exit ∧
          Encodes a fn {-1} (XCfg.init W x.length) (Fin.castAddEmb k') o
            (R.runFrom (Turing.Cfg.init entry x) t) ∧
          R.spaceUsed (Turing.Cfg.init entry x) t ≤
            sw + C * (W + (Nat.bits x.length).length + 1) := by
  obtain ⟨l, P, Ct, Ce, hP, hEnc, hB, hRad⟩ := startup_after_capture a ha fn Mw.k
  letI := P.finite
  letI := P.decEq
  let A := embedSilentRetTM (startupBank Mw.k (l + 1)) (startupCaptureIndex Mw.k (l + 1)) Mw.tm
  let ae : Mw.State ⊕ Unit := Sum.inl Mw.tm.q₀
  let ax : Mw.State ⊕ Unit := Sum.inr ()
  let R := seamCompTM A ax P.M P.entry
  let entry : (Mw.State ⊕ Unit) ⊕ P.S := Sum.inl ae
  let exit : (Mw.State ⊕ Unit) ⊕ P.S := Sum.inr P.exit
  let Ac := 8 + (l + 2)
  let Bc := startupTapeCount Mw.k l * (2 * Ce + 1)
  let C := Ct + 1 + Ac + Bc
  refine ⟨Mw.k + (l + 2), (Mw.State ⊕ Unit) ⊕ P.S, inferInstance, inferInstance,
    R, entry, exit, C, ?_⟩
  intro x W tw sw hMw hsw
  obtain ⟨tc, htc, hcut, data⟩ := startup_capture Mw (startupBank Mw.k (l + 1))
    (startupCaptureIndex Mw.k (l + 1)) (startupCapture_separated _ _) x W tw hMw
  let c := A.runFrom (Turing.Cfg.init ae x) tc
  change (∀ s < tc, (A.runFrom (Turing.Cfg.init ae x) s).state ≠ some ax) at hcut
  change c.state = some ax ∧
    c.workTapes (startupCaptureIndex Mw.k (l + 1)) = FinTM.bufferTape (Nat.bits W) ∧
    c.workTapePos (startupCaptureIndex Mw.k (l + 1)) = ((Nat.bits W).length : ℤ) ∧
    c.output = [] ∧ ∀ j, j ∉ Set.range (startupBank Mw.k (l + 1)) →
      j ≠ startupCaptureIndex Mw.k (l + 1) →
      c.workTapes j = (fun _ => none) ∧ c.workTapePos j = 0 at data
  obtain ⟨hc, hct, hcp, hco, hframe⟩ := data
  let d := c.mapState (fun _ => P.entry)
  have hd : d.state = some P.entry := by
    simp only [d, Cfg.mapState_state, hc, Option.map_some]
  have ready : startupReady Mw.k l W (startupErase d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [startupErase, d, Cfg.mapState_state, hc, Option.map_some]
    · simpa only [startupErase, d, Cfg.mapState_output] using hco
    · funext q
      simpa only [startupErase, d, Cfg.mapState_workTapes] using congrFun hct q
    · simpa only [startupErase, d, Cfg.mapState_workTapePos] using hcp
    · intro j hj hne
      obtain ⟨ht, hp⟩ := hframe j hj hne
      exact ⟨by
        funext q
        simpa only [startupErase, d, Cfg.mapState_workTapes] using congrFun ht q,
        by simpa only [startupErase, d, Cfg.mapState_workTapePos] using hp⟩
  have physical : P.pre W (startupErase d) := (hP W _).mpr ready
  have hp : (P.C x).pre W d := (P.pre_eq W d).mpr physical
  let tp := (P.C x).time W d
  let post := (P.C x).post W d
  have runP : P.M.runFrom d tp = post := (P.C x).run W d hd hp
  have exitP : post.state = some P.exit := Set.mem_singleton_iff.mp ((P.C x).exit_mem W d hd hp)
  have cutP : ∀ s < tp, (P.M.runFrom d s).state ≠ some P.exit := by
    intro s hs he
    exact (P.C x).cut W d hd hp s hs (Set.mem_singleton_iff.mpr he)
  have runA : A.runFrom (Turing.Cfg.init ae x) tc = c := rfl
  have hi : (Turing.Cfg.init (k := startupTapeCount Mw.k l) ae x).mapState
      (Sum.inl : Mw.State ⊕ Unit → (Mw.State ⊕ Unit) ⊕ P.S) = Turing.Cfg.init entry x :=
    startup_init_mapState ae Sum.inl x
  have run := seamCompTM_run_ofCfg A ax P.M P.entry runA hc hcut runP
  have cut := seamCompTM_firstReturn_ofCfg A ax P.M P.entry P.exit runA hc hcut runP exitP cutP
  rw [hi] at run cut
  refine ⟨tc + 1 + tp, fun _ => 0, ?_, cut, ?_, ?_, ?_⟩
  · let U := x.length + W ^ 2 + 1
    have hU : 1 ≤ U := by dsimp only [U]; omega
    have ht : tp ≤ Ct * U := (P.time_le W d hd physical).trans (hB x W)
    have hC : Ct + 1 ≤ C := by dsimp only [C]; omega
    calc
      _ ≤ tw + 1 + Ct * U := Nat.add_le_add (Nat.add_le_add_right htc 1) ht
      _ = tw + (Ct * U + 1) := by omega
      _ ≤ tw + ((Ct + 1) * U) := Nat.add_le_add_left (by
        calc
          _ ≤ Ct * U + U := Nat.add_le_add_left hU _
          _ = _ := by ring) tw
      _ ≤ tw + C * U := Nat.add_le_add_left (Nat.mul_le_mul_right U hC) tw
  · rw [run, Cfg.mapState_state, exitP]
    rfl
  · rw [run]
    simpa only [post, P.post_eq, startupAttach, startup_encodes_mapState] using hEnc W _ physical
  · let V := W + (Nat.bits x.length).length + 1
    have hV : 1 ≤ V := by dsimp only [V]; omega
    have hsp : P.M.spaceUsed d tp ≤ Bc * V := by
      have h := MultiTapeTM.spaceUsed_le_of_abs_le P.M d tp (Ce * V)
        (fun u hu j => hRad W d hd physical u hu j)
      exact h.trans (startup_space_factor (startupTapeCount Mw.k l) Ce V hV)
    have hsa : A.spaceUsed (Turing.Cfg.init ae x) tc ≤ sw + Ac * V := by
      have hs := startup_capture_space Mw (l + 1) x W tw hMw
      change A.spaceUsed (Turing.Cfg.init ae x) tw ≤
        Mw.tm.spaceUsed (Mw.tm.initCfg x) tw + Ac * ((Nat.bits W).length + 1) at hs
      calc
        _ ≤ A.spaceUsed (Turing.Cfg.init ae x) tw := A.spaceUsed_mono _ htc
        _ ≤ Mw.tm.spaceUsed (Mw.tm.initCfg x) tw + Ac * ((Nat.bits W).length + 1) := hs
        _ ≤ sw + Ac * V := Nat.add_le_add hsw (Nat.mul_le_mul_left Ac (by
          have hw := length_bits_le_self W
          dsimp only [V]
          omega))
    have hs := seamCompTM_spaceUsed_le_add_ofCfg A ax P.M P.entry (T₂ := tp) runA hc hcut
    rw [hi] at hs
    have hC : Ac + Bc ≤ C := by dsimp only [C]; omega
    calc
      _ ≤ A.spaceUsed (Turing.Cfg.init ae x) tc + P.M.spaceUsed d tp := hs
      _ ≤ (sw + Ac * V) + Bc * V := Nat.add_le_add hsa hsp
      _ = sw + (Ac + Bc) * V := by ring
      _ ≤ sw + C * V := Nat.add_le_add_left (Nat.mul_le_mul_right V hC) sw

end WordRAM.Sim
