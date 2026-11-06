/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-! ### The frame and the zero-tape case -/

/-- **Zero work tapes** [HS66; AB09, §1.7]: a binary machine `M` without work tapes has a binary
equivalent with two work tapes that reproduces each halting run of `t` steps within
`1 · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of `M`.

**Proof sketch.** Run `M` on the two-tape host through the forwarding embedding
`Turing.embedEmitTM` along the empty selection `Fin M.k ↪ Fin 2`, restarted at `M`'s initial
state. The host's initial configuration is the embedding of `M`'s into the blank frame with
heads at `0` and empty prefix (`Turing.embedEmitCfg_eq`, field by field from the `Cfg.init`
equations; the selected bank is empty). By `Turing.embedEmitTM_runFrom` the host's run is the
embedding of `M`'s run, so the two have the same state and the same output at every time
(`Turing.embedEmitCfg_state`, `Turing.embedEmitCfg_output`). Hence they halt together with the
same output, and `t ≤ (t + 1)(log₂(t + 1) + 1)` pads the time. -/
private theorem tt_zero_tapes (M : FinTM Bool) (hk : M.k = 0) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨σ⟩ : Nonempty (Fin M.k ↪ Fin 2) := ⟨Fin.castLEEmb (by omega)⟩
  -- the host: R1 of `M.tm`, restarted at `M`'s initial state
  obtain ⟨N, hq, hr⟩ : ∃ N : MultiTapeTM 2 Bool M.State,
      (∀ x, N.initCfg x = Cfg.init M.tm.q₀ x) ∧
        ∀ (x : List Bool) (c : Cfg 2 Bool M.State x) (t : ℕ),
          N.runFrom c t = (embedEmitTM σ M.tm).runFrom c t :=
    ⟨_, fun x => MultiTapeTM.initCfg_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ x,
      fun _ c t => MultiTapeTM.runFrom_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ c t⟩
  -- the host's initial configuration is the embedding of `M`'s into the blank frame
  have hinit : ∀ x : List Bool,
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.initCfg x) =
        Cfg.init M.tm.q₀ x := by
    intro x
    rw [MultiTapeTM.initCfg_eq]
    refine embedEmitCfg_eq σ _ _ [] _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Cfg.init_state]
    · simp only [Cfg.init_inputPos]
    · simp only [Cfg.init_output, List.append_nil]
    · intro i
      exact absurd i.isLt (by omega)
    · intro j _
      exact ⟨funext fun p => by simp only [Cfg.init_workTapes],
        by simp only [Cfg.init_workTapePos]⟩
  -- the host's run is the embedding of `M`'s
  have hrun : ∀ (x : List Bool) (t : ℕ), N.runFrom (N.initCfg x) t =
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.runFrom (M.tm.initCfg x) t) := by
    intro x t
    rw [hq, ← hinit x, hr, embedEmitTM_runFrom]
  refine ⟨{ k := 2, State := M.State, tm := N }, 1, rfl, fun x o t h => ?_, fun x o h => ?_⟩
  · obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
    have hb : t ≤ 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) :=
      calc t ≤ t + 1 := Nat.le_succ t
        _ = (t + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := (Nat.one_mul _).symm
    refine ComputesInTime.mono ?_ hb
    rw [computesInTime_iff]
    show (N.runFrom (N.initCfg x) t).state = none ∧ (N.runFrom (N.initCfg x) t).output = o
    refine ⟨?_, ?_⟩
    · rw [hrun, embedEmitCfg_state, hs]
    · rw [hrun, embedEmitCfg_output, ho, List.nil_append]
  · obtain ⟨t, ht⟩ := h
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ x o t).1 ht
    have hs' : (N.runFrom (N.initCfg x) t).state = none := hs
    have ho' : (N.runFrom (N.initCfg x) t).output = o := ho
    rw [hrun, embedEmitCfg_state] at hs'
    rw [hrun, embedEmitCfg_output, List.nil_append] at ho'
    exact ⟨t, (computesInTime_iff M x o t).2 ⟨hs', ho'⟩⟩

/-- **The frame of the two-work-tape reduction** [HS66; AB09, §1.7, with Claim 1.5 for the
alphabet]: let `HS` be a machine over the zone alphabet `Turing.ZoneSym M.k` with two work tapes
that reproduces each halting run of `M` of `t` steps on the encoded input `x.map Sum.inl`, with
the encoded output, within `c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of
which on an encoded input is the encoding of an output of `M`. Then `M` has a binary equivalent
with two work tapes, with the same overhead up to a constant, and whose completed outputs are
outputs of `M`.

**Proof sketch.** Reduce `HS` to the binary alphabet by `Turing.FinTM.alphabet_reduction_run`
along `Sum.inl : Bool ↪ ZoneSym M.k`, which keeps the two work tapes and multiplies the time by a
constant `c₂`; the constant of the result is `c₂ · c₁`. Forward, `M`'s run gives `HS`'s within
`c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and the reduction's forward direction gives the binary
machine's. Conversely, a completed output `w` of the binary machine comes from a completed output
`o'` of `HS` on the encoded input such that every binary word encoding to `o'` is `w`; the
converse property of `HS` writes `o'` as the encoding of an output `v` of `M`, so `v = w`. -/
private theorem tt_frame (M : FinTM Bool) (HS : FinTM (ZoneSym M.k)) (hHS : HS.k = 2) (c₁ : ℕ)
    (hfwd : ∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
      HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1))))
    (hconv : ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
      HS.ComputesInTime (x.map Sum.inl) o' t' →
        ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨c₂, M', hk, hf, hc⟩ :=
    alphabet_reduction_run (Function.Embedding.inl : Bool ↪ ZoneSym M.k) HS
  have hinl : ⇑(Function.Embedding.inl : Bool ↪ ZoneSym M.k) = Sum.inl :=
    funext fun b => Function.Embedding.inl_apply b
  rw [hinl] at hf hc
  refine ⟨M', c₂ * c₁, hk.trans hHS, fun x o t h => ?_, fun x o h => ?_⟩
  · rw [Nat.mul_assoc]
    exact hf x o _ (hfwd x o t h)
  · obtain ⟨t', o', ht', hv⟩ := hc x o h
    obtain ⟨t, v, hM, rfl⟩ := hconv x o' t' ht'
    obtain rfl := hv v rfl
    exact ⟨t, hM⟩

/-- **The route of the two-work-tape reduction** [HS66; AB09, §1.7]: if every binary machine
with at least one work tape has a two-work-tape zone machine with the forward property and the
image converse of `tt_frame`, then every binary machine has a binary equivalent with two work
tapes, with overhead `O((t + 1) log(t + 1))` per run of `t` steps, whose completed outputs are
outputs of the source.

**Proof sketch.** Without work tapes, `tt_zero_tapes`; otherwise the hypothesis gives the zone
machine, and `tt_frame` finishes. -/
private theorem tt_route
    (hHS : ∀ M : FinTM Bool, 1 ≤ M.k →
      ∃ (HS : FinTM (ZoneSym M.k)) (_ : HS.k = 2) (c₁ : ℕ),
        (∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
          HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
            (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
        ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
          HS.ComputesInTime (x.map Sum.inl) o' t' →
            ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl)
    (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  by_cases hk : M.k = 0
  · exact tt_zero_tapes M hk
  · obtain ⟨HS, hHSk, c₁, hf, hc⟩ := hHS M (by omega)
    exact tt_frame M HS hHSk c₁ hf hc

/-! ### The leaf: one simulated transition on the home cell -/

/-- The states of the transition step of the two-work-tape simulation of `M` [HS66; AB09,
§1.7]: `Sum.inl q`, about to simulate one transition of `M` at state `q`, and `Sum.inr (q', m)`,
the transition done, with `M`'s successor state `q'` and the head moves `m` still pending. -/
private abbrev tt_LeafSt (M : FinTM Bool) : Type :=
  M.State ⊕ (M.State × (Fin M.k → SignType))

/-- The input symbol of the binary source read through the zone alphabet's embedding
`Sum.inl` (a cell that holds no binary symbol reads as blank). -/
private def tt_decodeIn {k : ℕ} : Option (ZoneSym k) → Option Bool
  | some (.inl b) => some b
  | _ => none

/-- The home tuple read from the home cell of the zoned tape (`Turing.zonedTape`): track `t`
reads the virtual symbol stored in its slot, a blank or unoccupied slot reading as blank. -/
private def tt_homeRead {k : ℕ} (w : Option (ZoneSym k)) (t : Fin k) : Option Bool :=
  (zoneCellOfCell w t).join

/-- The value track `t` holds after one transition of `M` with action `a` from the home
tuple `v`: the written symbol, or the old one when nothing is written. -/
private def tt_homeNew {k : ℕ} {S : Type} (a : Action k Bool S) (v : Fin k → Option Bool)
    (t : Fin k) : Option Bool :=
  (a.workTapes t).1.getD (v t)

/-- The head moves of one transition of `M` with action `a`. -/
private def tt_moves {k : ℕ} {S : Type} (a : Action k Bool S) (t : Fin k) : SignType :=
  (a.workTapes t).2

/-- **The transition step's table** [HS66; AB09, §1.7]. No public row applies a finite-state
transition to the home cell of the zoned tape and the input head in one step, so the
simulation writes this one leaf. At `Sum.inl q` it reads the home tuple from the home cell of
tape `0` (`tt_homeRead`) and the input symbol through `Sum.inl` (`tt_decodeIn`), applies `M`'s
transition at `q`, writes the new home tuple, moves the input head as `M` does, emits `M`'s
output symbol through `Sum.inl`, keeps both work heads, and goes to `Sum.inr (q', m)` with `M`'s
successor state and head moves, or halts when `M` halts. A state `Sum.inr _` halts (it is
redirected by the host and never runs). -/
private def tt_leafTr (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) : Action 2 (ZoneSym M.k) (tt_LeafSt M) :=
  match s with
  | .inl q =>
    { inputTape := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).inputTape
      workTapes := fun j => if j = 0 then
          (some (some (.inr fun t =>
            some (tt_homeNew (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))
              (tt_homeRead (w 0)) t))), 0)
        else (none, 0)
      output := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).output.map Sum.inl
      state := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).state.map fun q' =>
        .inr (q', tt_moves (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))) }
  | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition step** [HS66; AB09, §1.7]: the two-tape machine over `Turing.ZoneSym M.k`
whose table is `tt_leafTr`. -/
private def tt_leafTM (M : FinTM Bool) : MultiTapeTM 2 (ZoneSym M.k) (tt_LeafSt M) where
  q₀ := .inl M.tm.q₀
  tr := tt_leafTr M

/-- The transition step keeps every work head. -/
private theorem tt_leafTM_tr_moves (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) (j : Fin 2) :
    (((tt_leafTM M).tr s inp w).workTapes j).2 = 0 := by
  rcases s with q | _
  · show (if j = 0 then _ else ((none : Option (Option (ZoneSym M.k))), (0 : SignType))).2 = 0
    split_ifs <;> rfl
  · rfl

/-- The transition step writes nothing on tape `1`. -/
private theorem tt_leafTM_tr_workTapes_of_ne (M : FinTM Bool) (q : M.State)
    (inp : Option (ZoneSym M.k)) (w : Fin 2 → Option (ZoneSym M.k)) {j : Fin 2} (hj : j ≠ 0) :
    ((tt_leafTM M).tr (.inl q) inp w).workTapes j = (none, 0) :=
  if_neg hj

/-- **One transition step** [HS66; AB09, §1.7]: from a configuration at `Sum.inl q`, one step
of the transition machine applies `M`'s transition `a` at `q` to the home tuple read from the
home cell and to the decoded input symbol. It writes the new home tuple into the cell under
head `0` and leaves tape `1`, moves the input head by `a`'s input move, keeps both work heads,
appends `a`'s output symbol through `Sum.inl`, and goes to `Sum.inr (q', m)` for `a`'s
successor `q'` and head moves `m`, or halts with `a`.

**Proof sketch.** `Turing.MultiTapeTM.step_of_some` applies the table's action; its fields are
read through `Turing.Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` and
`Turing.Action.apply_workTapes`, the table being this file's own definition. -/
private theorem tt_leaf_step (M : FinTM Bool) {x : List (ZoneSym M.k)}
    (c : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x) (q : M.State) (hc : c.state = some (.inl q)) :
    (tt_leafTM M).step c =
      { state := (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).state.map fun q' =>
          .inr (q', tt_moves (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))))
        inputPos := moveInputPos c.inputPos (M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).inputTape
        workTapes := fun j => if j = 0 then
            Function.update (c.workTapes 0) (c.workTapePos 0) (some (.inr fun t =>
              some (tt_homeNew (M.tm.tr q (tt_decodeIn c.inputSymbol)
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))))
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))) t)))
          else c.workTapes j
        workTapePos := c.workTapePos
        output := c.output ++ ((M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).output.map Sum.inl).toList } := by
  have hW : c.workTapeSymbols = fun i => c.workTapes i (c.workTapePos i) :=
    funext (Cfg.workTapeSymbols_eq c)
  rw [MultiTapeTM.step_of_some hc]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Action.apply_state, hW]
    rfl
  · rw [Action.apply_inputPos, hW]
    rfl
  · funext j p
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq, hW]
    by_cases hj : j = 0
    · subst hj
      rfl
    · rw [tt_leafTM_tr_workTapes_of_ne M q _ _ hj, Option.getD_none, Function.update_eq_self]
      show c.workTapes j p = (if j = 0 then _ else c.workTapes j) p
      rw [if_neg hj]
  · funext j
    rw [Action.apply_workTapePos, tt_leafTM_tr_moves, SignType.coe_zero, add_zero]
  · rw [Action.apply_output, hW]
    rfl

/-! ### The controller: the phase host over the transition step and the track steps -/

/-- **A track-step family** for `k` tracks with constant `A` [AB09, §1.7]: per direction `dir`
(`true` for a right move) and track `t`, a two-tape machine over `Turing.ZoneSym k` with finite
states, an entry, live exits, and per input a `Turing.Contract` with precondition
`Turing.zoneRowPre`, time at most `A · (2^{i₀} + 1)` for the scanned index `i₀`, and an endpoint
at the data `Turing.zoneTrackStepData dir t D` with the scratch head, the input head and the
output kept. `Turing.exists_zoneTrackStepTM` gives one. -/
private structure tt_Fam (k A : ℕ) where
  /-- the state types -/
  S : Bool → Fin k → Type
  /-- their finiteness -/
  fin : ∀ dir t, Fintype (S dir t)
  /-- their decidable equality -/
  dec : ∀ dir t, DecidableEq (S dir t)
  /-- the machines -/
  M : ∀ dir t, MultiTapeTM 2 (ZoneSym k) (S dir t)
  /-- the entries -/
  entry : ∀ dir t, S dir t
  /-- the exits -/
  X : ∀ dir t, Set (Option (S dir t))
  /-- the exits are live -/
  none_nmem : ∀ dir t, none ∉ X dir t
  /-- the contracts -/
  R : ∀ dir t (x : List (ZoneSym k)), Contract (M dir t) (entry dir t) (X dir t) (ZoneData k) x
  /-- their precondition -/
  pre : ∀ dir t x, (R dir t x).pre = zoneRowPre
  /-- their time and endpoint -/
  spec : ∀ dir t x (D : ZoneData k) (d : Cfg 2 (ZoneSym k) (S dir t) x),
    d.state = some (entry dir t) → zoneRowPre D d →
      (R dir t x).time D d ≤ A * (2 ^ zoneRebalanceIndex dir t D + 1) ∧
      zoneRowPre (zoneTrackStepData dir t D) ((R dir t x).post D d) ∧
      ((R dir t x).post D d).workTapePos 1 = d.workTapePos 1 ∧
      ((R dir t x).post D d).inputPos = d.inputPos ∧ ((R dir t x).post D d).output = d.output

/-- The direction of a head move: `true` for a right move, `false` otherwise. -/
private def tt_dir : SignType → Bool
  | .pos => true
  | _ => false

/-- The phase index of the simulation: `none` for the transition step, `some (q', m, t)` for
the step of track `t` in the round whose transition went to `q'` with head moves `m`. -/
private abbrev tt_I (M : FinTM Bool) : Type :=
  Option (M.State × (Fin M.k → SignType) × Fin M.k)

/-- The phases' state types: the transition step's, and per track the track step's of its
direction. -/
private def tt_Ph (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) : tt_I M → Type
  | none => tt_LeafSt M
  | some (_, m, t) => F.S (tt_dir (m t)) t

/-- The phases' machines: the transition step, and per track the track step of its
direction (for a stay, it is entered and left at once). -/
private def tt_Mf (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → MultiTapeTM 2 (ZoneSym M.k) (tt_Ph M F i)
  | none => tt_leafTM M
  | some (_, m, t) => F.M (tt_dir (m t)) t

/-- The state after the step of track `t`: the next track's entry, or the transition step at
`q'` after the last track. -/
private def tt_next (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (t : Fin M.k) : Σ i, tt_Ph M F i :=
  if h : t.val + 1 < M.k then
    ⟨some (q', m, ⟨t.val + 1, h⟩), F.entry (tt_dir (m ⟨t.val + 1, h⟩)) ⟨t.val + 1, h⟩⟩
  else ⟨none, .inl q'⟩

open Classical in
/-- **The redirects** of the simulation's phase host: the transition step's exit
`Sum.inr (q', m)` goes to track `0`'s entry; a track's exit (for a stay, its entry) goes to
`tt_next`; nothing else is redirected. -/
private noncomputable def tt_red (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    (i : tt_I M) → tt_Ph M F i → Option (Σ i, tt_Ph M F i)
  | none, .inl _ => none
  | none, .inr (q', m) => some ⟨some (q', m, ⟨0, hk⟩), F.entry (tt_dir (m ⟨0, hk⟩)) ⟨0, hk⟩⟩
  | some (q', m, t), s =>
    if (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)
    then some (tt_next M F q' m t) else none

open Classical in
/-- A track's exit (for a stay, its entry) is redirected to `tt_next`. -/
private theorem tt_red_track_pos (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)) :
    tt_red M F hk (some (q', m, t)) s = some (tt_next M F q' m t) :=
  if_pos h

open Classical in
/-- Every other state of a track's phase is not redirected. -/
private theorem tt_red_track_neg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : ¬((m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨
      (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t))) :
    tt_red M F hk (some (q', m, t)) s = none :=
  if_neg h

/-- The phases' state types are finite. -/
private def tt_phFin (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → Fintype (tt_Ph M F i)
  | none => inferInstanceAs (Fintype (tt_LeafSt M))
  | some (_, m, t) => F.fin (tt_dir (m t)) t

/-- The phases' state types have decidable equality. -/
private def tt_phDec (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → DecidableEq (tt_Ph M F i)
  | none => inferInstanceAs (DecidableEq (tt_LeafSt M))
  | some (_, m, t) => F.dec (tt_dir (m t)) t

/-- **The two-work-tape zone machine** [HS66; AB09, §1.7]: the phase host
`Turing.phaseHostTM` over the transition step and the track steps of `F`, started at the
transition step at `M`'s initial state. Tape `0` is the zoned tape, tape `1` the scratch
tape. -/
private noncomputable def tt_HS (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    FinTM (ZoneSym M.k) :=
  letI := tt_phFin M F
  letI := tt_phDec M F
  { k := 2
    State := Σ i, tt_Ph M F i
    tm := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) }

/-! ### The configurations at the round boundaries -/

/-- **A configuration at a phase boundary**: state `s`, input head at `ip`, output `out`, tape
`0` the zoned tape of `D` with its head at home, tape `1` blank with its head at `0`. -/
private def tt_cfg {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) : Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then zonedTape D.2 else fun _ => none, fun _ => 0, out⟩

/-- Renaming the state of a phase-boundary configuration renames its state only. -/
private theorem tt_cfg_mapState {k : ℕ} {S S' : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) (f : S → S') :
    (tt_cfg s D ip out).mapState f = (tt_cfg (s.map f) D ip out : Cfg 2 (ZoneSym k) S' x) :=
  Cfg.mapState_eq_of_fields _ f _ rfl rfl rfl rfl rfl

/-- A phase-boundary configuration satisfies the zone rows' precondition. -/
private theorem tt_cfg_rowPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    zoneRowPre D (tt_cfg s D ip out : Cfg 2 (ZoneSym k) S x) :=
  (zoneRowPre_iff D _).mpr ⟨rfl, rfl, fun _ => rfl⟩

/-- **A row endpoint is a phase-boundary configuration**: a configuration that satisfies the
zone rows' precondition at `D`, with head `1` at `0`, input head `ip` and output `out`, is
`tt_cfg` at `D` once its state is renamed to the constant `s`, if it is live.

**Proof sketch.** Field by field (`Turing.Cfg.mapState_eq_of_fields`): the state is `some s`
since `d` is live; tape `0` and head `0` are the precondition's (`Turing.zoneRowPre_iff`), tape `1`
is blank by it, head `1` is `h1`, and the input head and the output are the hypotheses. -/
private theorem tt_mapState_eq_cfg {k : ℕ} {S S' : Type} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (hp : zoneRowPre D d) (s : S')
    (hs : d.state.isSome) (h1 : d.workTapePos 1 = 0) (ip : Fin (x.length + 2))
    (hi : d.inputPos = ip) (out : List (ZoneSym k)) (ho : d.output = out) :
    d.mapState (fun _ => s) = tt_cfg (some s) D ip out := by
  obtain ⟨h0, hp0, hb⟩ := (zoneRowPre_iff D d).mp hp
  obtain ⟨s₀, hs₀⟩ := Option.isSome_iff_exists.mp hs
  refine Cfg.mapState_eq_of_fields d _ _ ?_ hi ?_ ?_ ho
  · rw [hs₀]
    rfl
  · funext j p
    by_cases hj : j = 0
    · subst hj
      rw [h0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [hb p]
      rfl
  · funext j
    by_cases hj : j = 0
    · subst hj
      rw [hp0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [h1]
      rfl

/-! ### One track's phase -/

/-- The data after track `t`'s step for head move `s`: unchanged for a stay, otherwise
`Turing.zoneTrackStepData` in the move's direction. -/
private def tt_trackData {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ZoneData k :=
  if s = 0 then D else zoneTrackStepData (tt_dir s) t D

/-- The scanned index of track `t`'s step for head move `s`: `0` for a stay. -/
private def tt_idx {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ℕ :=
  if s = 0 then 0 else zoneRebalanceIndex (tt_dir s) t D

/-- The time of track `t`'s phase before its dispatch step: `0` for a stay, otherwise the
track step's contract time from the phase-boundary configuration. -/
private def tt_trackTime (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (t : Fin M.k) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) : ℕ :=
  if m t = 0 then 0 else
    (F.R (tt_dir (m t)) t x).time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)

/-- **One track's phase** [HS66; AB09, §1.7]: from the entry of track `t`'s phase, at a
phase-boundary configuration with data `D`, the zone machine runs live for the phase's time
plus one dispatch step to the phase-boundary configuration at `tt_next` with the data after
track `t`'s step, the input head and the output kept; the phase's time is at most
`A · (2^{i₀} + 1)` for its scanned index `i₀`.

**Proof sketch.** A stay is redirected at once (`Turing.phaseHostTM_run` with time `0`). A move
runs the track step's contract inside the host (`Turing.phaseHostTM_run`): its run gives the
phase run, its cut and the redirect table give the guard, and its live exit is redirected to
`tt_next`. The endpoint satisfies the rows' precondition at the new data and keeps head `1`,
the input head and the output, so it is the phase-boundary configuration there
(`tt_mapState_eq_cfg`). Liveness before the end is the contract's (`Turing.Contract.live`). -/
private theorem tt_track_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k)
    (D : ZoneData M.k) (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out)
        (tt_cfg (some (tt_next M F q' m t)) (tt_trackData (m t) t D) ip out)
        (tt_trackTime M F x m t D ip out + 1) ∧
      tt_trackTime M F x m t D ip out ≤ A * (2 ^ tt_idx (m t) t D + 1) := by
  set c : Cfg 2 (ZoneSym M.k) (tt_Ph M F (some (q', m, t))) x :=
    tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out with hc
  have hb : (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out :
      Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x) = c.mapState (Sigma.mk (some (q', m, t))) :=
    (tt_cfg_mapState (S := tt_Ph M F (some (q', m, t))) (some (F.entry (tt_dir (m t)) t)) D ip
      out (Sigma.mk (β := tt_Ph M F) (some (q', m, t)))).symm
  rw [hb]
  by_cases h0 : m t = 0
  · -- a stay: redirected at once
    have hred : tt_red M F hk (some (q', m, t)) (F.entry (tt_dir (m t)) t) =
        some (tt_next M F q' m t) := by
      exact tt_red_track_pos M F hk q' m t _ (Or.inl ⟨h0, rfl⟩)
    have H := phaseHostTM_run (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) (some (q', m, t))
      c c 0 MultiTapeTM.runFrom_zero (F.entry (tt_dir (m t)) t) rfl _ hred
      (fun u hu => absurd hu (Nat.not_lt_zero u))
    have hT : tt_trackTime M F x m t D ip out = 0 := if_pos h0
    have hD : tt_trackData (m t) t D = D := if_pos h0
    rw [hT, hD]
    refine ⟨(segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩, Nat.zero_le _⟩
    · rw [H.2, hc, tt_cfg_mapState]
      rfl
    · obtain rfl : u = 0 := by omega
      rw [MultiTapeTM.runFrom_zero, Set.mem_singleton_iff, Cfg.mapState_state]
      exact fun h => by cases h
  · -- a move: the track step's contract inside the host
    set R := F.R (tt_dir (m t)) t x with hR
    have hpre : R.pre D c := by
      rw [hR, F.pre]
      exact tt_cfg_rowPre _ D ip out
    obtain ⟨htime, hpost, h1, hin, hout⟩ := F.spec (tt_dir (m t)) t x D c rfl
      (tt_cfg_rowPre _ D ip out)
    have hx := R.exit_mem D c rfl hpre
    obtain ⟨s', hs'⟩ : ∃ s', (R.post D c).state = some s' := by
      cases h : (R.post D c).state with
      | none => rw [h] at hx; exact absurd hx (F.none_nmem _ _)
      | some s' => exact ⟨s', rfl⟩
    have hs'X : some s' ∈ F.X (tt_dir (m t)) t := hs' ▸ hx
    have hred : tt_red M F hk (some (q', m, t)) s' = some (tt_next M F q' m t) := by
      exact tt_red_track_pos M F hk q' m t _ (Or.inr ⟨h0, hs'X⟩)
    have hguard : ∀ u < R.time D c, ∀ s,
        ((tt_Mf M F (some (q', m, t))).runFrom c u).state = some s →
          tt_red M F hk (some (q', m, t)) s = none := by
      intro u hu s hs
      refine tt_red_track_neg M F hk q' m t _ ?_
      rintro (⟨h, -⟩ | ⟨-, hm⟩)
      · exact h0 h
      · exact R.cut D c rfl hpre u hu (hs ▸ hm)
    have H := phaseHostTM_run (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) (some (q', m, t))
      c (R.post D c) (R.time D c) (R.run D c rfl hpre) s' hs' _ hred hguard
    have hT : tt_trackTime M F x m t D ip out = R.time D c := if_neg h0
    have hD : tt_trackData (m t) t D = zoneTrackStepData (tt_dir (m t)) t D := if_neg h0
    have hI : tt_idx (m t) t D = zoneRebalanceIndex (tt_dir (m t)) t D := if_neg h0
    rw [hT, hD, hI]
    refine ⟨(segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩, htime⟩
    · rw [H.2]
      exact tt_mapState_eq_cfg _ _ hpost _ (by rw [hs']; rfl) h1 ip hin out hout
    · rw [H.1 u (by omega), Set.mem_singleton_iff, Cfg.mapState_state]
      intro h
      rcases Nat.lt_or_ge u (R.time D c) with hlt | hge
      · exact R.live D c rfl hpre hlt (Option.map_eq_none_iff.mp h)
      · obtain rfl : u = R.time D c := by omega
        rw [R.run D c rfl hpre, hs'] at h
        cases h

/-! ### One round: the transition step, then every track -/

/-- **A round's start configuration** at the transition step: tape `0` is the zoned tape of `D`
except at the home cell, which holds `h0`; the rest as in `tt_cfg`. The first round starts with
a blank home cell, every later one with the zoned tape's own. -/
private def tt_cfg0 {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (h0 : Option (ZoneSym k)) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then Function.update (zonedTape D.2) 0 h0 else fun _ => none,
    fun _ => 0, out⟩

/-- The transition of `M` at `q` on input symbol `inp` from the homes of `D`. -/
private def tt_act (M : FinTM Bool) (q : M.State) (inp : Option Bool) (D : ZoneData M.k) :
    Action M.k Bool M.State :=
  M.tm.tr q inp fun t => (D.2 t).home

/-- The data after the home write of action `a`. -/
private def tt_homeData {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) :
    ZoneData k :=
  ⟨D.1, fun t => zoneHomeWrite (D.2 t) (tt_homeNew a (fun t => (D.2 t).home) t)⟩

/-- The data after the steps of the tracks below `j`, for head moves `m`, from `D`. -/
private def tt_Dtr {k : ℕ} (m : Fin k → SignType) (D : ZoneData k) : ℕ → ZoneData k
  | 0 => D
  | j + 1 => if h : j < k then tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m D j) else tt_Dtr m D j

/-- The state at the start of track `j`'s phase, or the transition step at `q'` after the
last track. -/
private def tt_stAt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (j : ℕ) : Σ i, tt_Ph M F i :=
  if h : j < M.k then ⟨some (q', m, ⟨j, h⟩), F.entry (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩⟩
  else ⟨none, .inl q'⟩

/-- The time of track `j`'s phase in a round, with its dispatch step. -/
private def tt_τ (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (j : ℕ) : ℕ :=
  if h : j < M.k then tt_trackTime M F x m ⟨j, h⟩ (tt_Dtr m D j) ip out + 1 else 0

/-- **The tracks of a round** [HS66; AB09, §1.7]: from track `0`'s entry, the zone machine runs
live through every track's phase in order, to the transition step at `q'` with the data after
every track's step, in `∑ j < k` of the phases' times.

**Proof sketch.** `Turing.Segment.iterate_seq` over the tracks, each track by `tt_track_seg`;
consecutive boundaries match because `tt_next` at track `j` is `tt_stAt` at `j + 1`. -/
private theorem tt_tracks_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cfg (some (tt_stAt M F q' m 0)) D ip out)
      (tt_cfg (some ⟨none, .inl q'⟩) (tt_Dtr m D M.k) ip out)
      (∑ j ∈ Finset.range M.k, tt_τ M F x m D ip out j) := by
  have hend : tt_stAt M F q' m M.k = ⟨none, .inl q'⟩ := dif_neg (lt_irrefl _)
  have H := Segment.iterate_seq
    (M := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) (F := {none})
    (P := fun _ => True)
    (fun j => (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out :
      Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x))
    (tt_τ M F x m D ip out) trivial M.k (fun j hj => ?_)
  · dsimp only at H
    rw [hend] at H
    exact H
  · have hs : tt_stAt M F q' m j = ⟨some (q', m, ⟨j, hj⟩), F.entry (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩⟩ :=
      dif_pos hj
    have hn : tt_next M F q' m ⟨j, hj⟩ = tt_stAt M F q' m (j + 1) := rfl
    have hD : tt_Dtr m D (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) := dif_pos hj
    have hτ : tt_τ M F x m D ip out j = tt_trackTime M F x m ⟨j, hj⟩ (tt_Dtr m D j) ip out + 1 :=
      dif_pos hj
    show Segment _ _ _ (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out)
      (tt_cfg (some (tt_stAt M F q' m (j + 1))) (tt_Dtr m D (j + 1)) ip out) _
    rw [hs, hD, hτ, ← hn]
    exact (tt_track_seg M F hk q' m ⟨j, hj⟩ (tt_Dtr m D j) ip out).1

/-- **One round** [HS66; AB09, §1.7]. From the transition step at `q`, with data `D` whose
homes are what the home cell `h0` reads and with decoded input symbol `inp`, let `a` be `M`'s
transition at `q` on `inp` and the homes of `D`. If `a` halts, the zone machine halts after one
step with `a`'s output symbol appended. Otherwise, with successor `q'`, it runs live to the
transition step at `q'`, with the data after the home write and every track's step, the input
head moved by `a` and `a`'s output symbol appended, in `2 + ∑ j < k` of the tracks' phase times.

**Proof sketch.** One transition step (`tt_leaf_step`) writes the home tuple: the home cell
becomes the zoned tape's of the written data (`Turing.zonedTape_homeWrite`). In the host it is
the tagged phase run (`Turing.phaseHostTM_run_le`, for a halt) or, with the redirect of its
exit, two steps to track `0`'s entry (`Turing.phaseHostTM_run`); the tracks follow
(`tt_tracks_seg`) and the two segments concatenate (`Turing.Segment.trans`). -/
private theorem tt_round (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q : M.State) (D : ZoneData M.k) (h0 : Option (ZoneSym M.k))
    (hread : ∀ t, tt_homeRead h0 t = (D.2 t).home) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (inp : Option Bool)
    (hinp : tt_decodeIn (tt_cfg0 (some (.inl q)) D h0 ip out :
      Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).inputSymbol = inp) :
    ((tt_act M q inp D).state = none →
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).output =
        out ++ ((tt_act M q inp D).output.map Sum.inl).toList) ∧
    ∀ q', (tt_act M q inp D).state = some q' →
      Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        ((tt_cfg0 (some (.inl q)) D h0 ip out :
          Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none))
        (tt_cfg (some ⟨none, .inl q'⟩)
          (tt_Dtr (tt_moves (tt_act M q inp D)) (tt_homeData (tt_act M q inp D) D) M.k)
          (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList))
        (2 + ∑ j ∈ Finset.range M.k, tt_τ M F x (tt_moves (tt_act M q inp D))
          (tt_homeData (tt_act M q inp D) D) (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList) j) := by
  set c₀ : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x := tt_cfg0 (some (.inl q)) D h0 ip out with hc₀
  set a := tt_act M q inp D with ha
  have hr : c₀.workTapes 0 (c₀.workTapePos 0) = h0 := by
    show Function.update (zonedTape D.2) 0 h0 0 = h0
    exact Function.update_self _ _ _
  have hR : tt_homeRead h0 = fun t => (D.2 t).home := funext hread
  have hstep := tt_leaf_step M c₀ q rfl
  rw [hr, hR, hinp] at hstep
  change (tt_leafTM M).step c₀ =
    { state := a.state.map fun q' => .inr (q', tt_moves a)
      inputPos := moveInputPos c₀.inputPos a.inputTape
      workTapes := fun j => if j = 0 then
          Function.update (c₀.workTapes 0) (c₀.workTapePos 0)
            (some (.inr fun t => some (tt_homeNew a (fun t => (D.2 t).home) t)))
        else c₀.workTapes j
      workTapePos := c₀.workTapePos
      output := c₀.output ++ (a.output.map Sum.inl).toList } at hstep
  have h1 : (tt_Mf M F none).runFrom c₀ 1 = (tt_leafTM M).step c₀ := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  have hguard : ∀ u < 1, ∀ s, ((tt_Mf M F none).runFrom c₀ u).state = some s →
      tt_red M F hk none s = none := by
    intro u hu s hs
    obtain rfl : u = 0 := by omega
    rw [MultiTapeTM.runFrom_zero] at hs
    obtain rfl : (Sum.inl q : tt_LeafSt M) = s := Option.some.inj hs
    rfl
  refine ⟨fun hn => ?_, fun q' hq' => ?_⟩
  · have H := phaseHostTM_run_le (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ 1
      hguard 1 le_rfl
    rw [H, h1, hstep]
    refine ⟨?_, ?_⟩
    · rw [Cfg.mapState_state]
      show Option.map _ (a.state.map _) = none
      rw [hn]
      rfl
    · rw [Cfg.mapState_output]
      rfl
  · have hs₁ : ((tt_leafTM M).step c₀).state = some (.inr (q', tt_moves a)) := by
      rw [hstep]
      show a.state.map _ = _
      rw [hq']
      rfl
    have hred : tt_red M F hk none (.inr (q', tt_moves a)) =
        some (tt_stAt M F q' (tt_moves a) 0) := by
      show some _ = some _
      rw [show tt_stAt M F q' (tt_moves a) 0 = _ from dif_pos hk]
    have H := phaseHostTM_run (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ _ 1 h1
      _ hs₁ _ hred hguard
    have hend : ((tt_leafTM M).step c₀).mapState (fun _ => tt_stAt M F q' (tt_moves a) 0) =
        tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList) := by
      refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
      · rw [hs₁]
        rfl
      · rw [hstep]
        rfl
      · rw [hstep]
        funext j p
        by_cases hj : j = 0
        · subst hj
          show Function.update (Function.update (zonedTape D.2) 0 h0) 0 _ p = zonedTape _ p
          rw [Function.update_idem, zonedTape_homeWrite]
          rfl
        · show (if j = 0 then _ else c₀.workTapes j) p = (if j = 0 then _ else fun _ => none) p
          rw [if_neg hj, if_neg hj]
          show (if j = 0 then _ else fun _ => none) p = none
          rw [if_neg hj]
      · rw [hstep]
        rfl
      · rw [hstep]
        rfl
    have hlead : Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True) (c₀.mapState (Sigma.mk none))
        (tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList)) 2 := by
      refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
      · exact H.2.trans hend
      · rw [H.1 u (by omega), Set.mem_singleton_iff, Cfg.mapState_state]
        rcases Nat.lt_or_ge u 1 with h | h
        · obtain rfl : u = 0 := by omega
          rw [MultiTapeTM.runFrom_zero]
          exact fun h => by cases h
        · obtain rfl : u = 1 := by omega
          rw [h1, hs₁]
          exact fun h => by cases h
    exact hlead.trans (tt_tracks_seg M F hk q' (tt_moves a) (tt_homeData a D) _ _)

/-- **The time bound of a round's track phases** [AB09, §1.7]: track `j`'s phase, with its
dispatch, takes at most `A · (2^{i₀} + 1) + 1` steps for its scanned index `i₀` (`0` for a
stay). -/
private theorem tt_τ_le (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List (ZoneSym M.k)) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) (j : ℕ) (hj : j < M.k) :
    tt_τ M F x m D ip out j ≤ A * (2 ^ tt_idx (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) + 1) + 1 := by
  rw [show tt_τ M F x m D ip out j =
    tt_trackTime M F x m ⟨j, hj⟩ (tt_Dtr m D j) ip out + 1 from dif_pos hj]
  have := (tt_track_seg M F hk (x := x) M.tm.q₀ m ⟨j, hj⟩ (tt_Dtr m D j) ip out).2
  omega

/-! ### The target -/

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the `log₂ t + 1` zones a
run of `t` steps reaches gives `O(t log t)` steps in all. The converse holds because `M'` writes
an output symbol exactly when `M` does, in the same order, and halts only when `M` halts. With
no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  refine tt_route (fun M hk => ?_) M
  sorry

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end Turing.FinTM
