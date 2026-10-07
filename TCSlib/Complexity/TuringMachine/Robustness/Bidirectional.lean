/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bidirectional versus unidirectional tapes

[AB09, Claim 1.8]: tapes that are infinite in both directions are simulated by tapes
infinite in one direction only, with constant-factor slowdown.

## Deviations from [AB09]

Our vendored model's tapes are *already* bidirectional (`ℤ`-indexed) — that choice is
what lets initialization dispense with start markers. So the faithful in-model
rendering of Claim 1.8 runs in the only meaningful direction: every machine is
simulated, with constant-factor slowdown and the same number of work tapes, by one
whose work heads **never visit a negative cell** (`Turing.FinTM.NonnegativeHeads`),
i.e. by a machine that uses its tapes unidirectionally. The simulating machine "folds"
each tape at the origin, following [AB09]'s proof, over the enlarged non-blank
alphabet `Bool × Option Γ × Option Γ` — an origin flag plus two *independent*,
possibly blank, payloads. (A bare `Γ × Γ` cannot represent a symbol paired with a
blank neighbor; phase-2 re-audit, finding 1.)

## Main results

* `Turing.FinTM.NonnegativeHeads` — the unidirectional-use predicate.
* `Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.8, p. 18.)
-/

namespace Turing.FinTM

/-- A machine uses its work tapes unidirectionally: in every initialized run, no work
head ever visits a negative cell. -/
def NonnegativeHeads {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (input : List Γ) (t : ℕ) (i : Fin M.k),
    0 ≤ (M.tm.runFrom (M.tm.initCfg input) t).workTapePos i

private abbrev FoldSymbol (Γ : Type) := Bool × Option Γ × Option Γ

private def foldEmbedding {Γ : Type} : Γ ↪ FoldSymbol Γ where
  toFun a := (false, some a, none)
  inj' := by intro a b h; exact Option.some.inj (congrArg (fun x => x.2.1) h)

private def foldPos (z : ℤ) : ℤ := if 0 ≤ z then z else -z - 1

private def foldSide (z : ℤ) : Bool := decide (0 ≤ z)

private def foldPack {Γ : Type} (v : FoldSymbol Γ) : Option (FoldSymbol Γ) :=
  match v with
  | (false, none, none) => none
  | _ => some v

private def foldUnpack {Γ : Type} (v : Option (FoldSymbol Γ)) : FoldSymbol Γ :=
  v.getD (false, none, none)

private lemma foldUnpack_pack {Γ : Type} (v : FoldSymbol Γ) :
    foldUnpack (foldPack v) = v := by
  rcases v with ⟨b, a, c⟩
  cases b <;> cases a <;> cases c <;> rfl

private def foldTape {Γ : Type} (t : ℤ → Option Γ) (p : ℤ) : Option (FoldSymbol Γ) :=
  if 0 ≤ p then foldPack (decide (p = 0), t p, t (-p - 1)) else none

private def foldMove (side origin : Bool) (d : SignType) : SignType × Bool :=
  match side, d with
  | true, .pos => (.pos, true)
  | true, .neg => if origin then (.zero, false) else (.neg, true)
  | false, .neg => (.pos, false)
  | false, .pos => if origin then (.zero, true) else (.neg, false)
  | _, .zero => (.zero, side)

private lemma foldPos_nonneg (z : ℤ) : 0 ≤ foldPos z := by
  unfold foldPos
  split <;> omega

private lemma foldMove_correct (z : ℤ) (d : SignType) :
    foldPos z + ((foldMove (foldSide z) (decide (foldPos z = 0)) d).1 : ℤ) =
        foldPos (z + (d : ℤ)) ∧
      (foldMove (foldSide z) (decide (foldPos z = 0)) d).2 =
        foldSide (z + (d : ℤ)) := by
  by_cases hz : 0 ≤ z <;> cases d <;>
    simp [foldMove, foldSide, foldPos, hz, SignType.cast] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

private def foldRead {Γ : Type} (side : Bool) (w : Option (FoldSymbol Γ)) : Option Γ :=
  if side then (foldUnpack w).2.1 else (foldUnpack w).2.2

private lemma foldRead_tape {Γ : Type} (t : ℤ → Option Γ) (z : ℤ) :
    foldRead (foldSide z) (foldTape t (foldPos z)) = t z := by
  unfold foldRead
  rw [foldTape, if_pos (foldPos_nonneg z), foldUnpack_pack]
  unfold foldSide foldPos
  split_ifs <;> simp_all

private def foldWrite {Γ : Type} (side : Bool) (w : Option (FoldSymbol Γ))
    (a : Option Γ) : Option (FoldSymbol Γ) :=
  let v := foldUnpack w
  foldPack (v.1, if side then a else v.2.1, if side then v.2.2 else a)

/-- Updating a virtual cell changes only its active folded payload. At the folded
coordinate, split on the virtual head's sign; away from it neither paired virtual
coordinate equals the updated cell. Canonical packing preserves physical blanks. -/
private lemma foldTape_update {Γ : Type} [DecidableEq Γ]
    (t : ℤ → Option Γ) (z : ℤ) (a : Option Γ) :
    Function.update (foldTape t) (foldPos z)
        (foldWrite (foldSide z) (foldTape t (foldPos z)) a) =
      foldTape (Function.update t z a) := by
  funext p
  unfold foldWrite
  rw [foldTape, if_pos (foldPos_nonneg z), foldUnpack_pack]
  by_cases hp : p = foldPos z
  · subst p
    rw [Function.update_self]
    unfold foldTape
    rw [if_pos (foldPos_nonneg z)]
    have hn : -z - 1 ≠ z := by omega
    by_cases hz : 0 ≤ z
    · simp [foldSide, foldPos, hz, Function.update_apply, hn]
    · simp [foldSide, foldPos, hz, Function.update_apply, hn]
  · rw [Function.update_of_ne hp]
    unfold foldTape
    split_ifs with h
    · have h₁ : p ≠ z := by unfold foldPos at hp; split_ifs at hp <;> omega
      have h₂ : -p - 1 ≠ z := by unfold foldPos at hp; split_ifs at hp <;> omega
      rw [Function.update_of_ne h₁, Function.update_of_ne h₂]
    · rfl

private def foldAction {Γ S : Type} {k : ℕ} (side : Fin k → Bool)
    (work : Fin k → Option (FoldSymbol Γ)) (a : Action k Γ S) :
    Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) where
  inputTape := a.inputTape
  workTapes i :=
    ((a.workTapes i).1.map (foldWrite (side i) (work i)),
      (foldMove (side i) (foldUnpack (work i)).1 (a.workTapes i).2).1)
  output := a.output.map foldEmbedding
  state := a.state.map fun q => some (q, fun i =>
    (foldMove (side i) (foldUnpack (work i)).1 (a.workTapes i).2).2)

private def foldCfg {Γ S : Type} {k : ℕ} {x : List Γ} (c : Cfg k Γ S x) :
    Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) (x.map foldEmbedding) where
  state := c.state.map fun q => some (q, fun i => foldSide (c.workTapePos i))
  inputPos := ⟨c.inputPos.val, by simp only [List.length_map]; exact c.inputPos.isLt⟩
  workTapes i := foldTape (c.workTapes i)
  workTapePos i := foldPos (c.workTapePos i)
  output := c.output.map foldEmbedding

private lemma foldCfg_input {Γ S : Type} {k : ℕ} {x : List Γ} (c : Cfg k Γ S x) :
    (foldCfg c).inputSymbol = c.inputSymbol.map foldEmbedding := by
  unfold Cfg.inputSymbol
  simp only [foldCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private lemma foldCfg_origin {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (i : Fin k) :
    (foldUnpack ((foldCfg c).workTapeSymbols i)).1 =
      decide (foldPos (c.workTapePos i) = 0) := by
  simp only [Cfg.workTapeSymbols, foldCfg, foldTape, if_pos (foldPos_nonneg _),
    foldUnpack_pack]

/-- Folding an action preserves the full configuration representation. The tape
identity updates precisely one of the two independent payloads, and the movement
identity covers both stationary crossings of the fold. -/
private lemma foldCfg_apply {Γ S : Type} [DecidableEq Γ] {k : ℕ} {x : List Γ}
    (a : Action k Γ S) (c : Cfg k Γ S x) :
    (foldAction (fun i => foldSide (c.workTapePos i)) (foldCfg c).workTapeSymbols a).apply
      (foldCfg c) = foldCfg (a.apply c) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · change a.state.map _ = a.state.map _
    congr 1
    funext q
    congr 2
    funext i
    rw [foldCfg_origin]
    exact (foldMove_correct (c.workTapePos i) (a.workTapes i).2).2
  · apply Fin.ext
    simp [foldCfg, foldAction, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    cases hw : (a.workTapes i).1 with
    | none => simp [foldAction, Action.apply, foldCfg, hw]
    | some w =>
      simpa only [foldAction, Option.map_some, foldCfg, Action.apply, hw, Cfg.workTapeSymbols] using
        foldTape_update (c.workTapes i) (c.workTapePos i) w
  · funext i
    change foldPos (c.workTapePos i) +
      ((foldMove (foldSide (c.workTapePos i))
        (foldUnpack ((foldCfg c).workTapeSymbols i)).1 (a.workTapes i).2).1 : ℤ) = _
    rw [foldCfg_origin]
    exact (foldMove_correct (c.workTapePos i) (a.workTapes i).2).1
  · simp [foldAction, foldCfg, Action.apply, List.map_append, Option.toList_map]

private def foldDecode {Γ : Type} : FoldSymbol Γ → Option Γ
  | (false, some a, none) => some a
  | _ => none

private def foldHalt {Γ S : Type} {k : ℕ} : Action k Γ S :=
  ⟨0, fun _ => (none, 0), none, none⟩

private def foldInitAction {Γ S : Type} {k : ℕ} (q : S) :
    Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) :=
  ⟨0, fun _ => (some (some (true, none, none)), 0), none,
    some (some (q, fun _ => true))⟩

/-- Initialize every origin, halting on the same transition if the first input
read is already outside the embedding. No simulated transition precedes the check. -/
private def foldStartAction {Γ S : Type} {k : ℕ} (q : S)
    (inp : Option (FoldSymbol Γ)) : Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) :=
  match inp with
  | none => foldInitAction q
  | some v => match foldDecode v with
    | none => { foldInitAction q with state := none }
    | some _ => foldInitAction q

private lemma foldStartAction_embed {Γ S : Type} {k : ℕ} (q : S) (inp : Option Γ) :
    foldStartAction (k := k) q (inp.map foldEmbedding) = foldInitAction q := by
  cases inp <;> rfl

private def foldTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ) :
    FinTM (FoldSymbol Γ) where
  k := M.k
  State := Option (M.State × (Fin M.k → Bool))
  tm :=
    { q₀ := none
      tr := fun q inp work => match q with
        | none => foldStartAction M.tm.q₀ inp
        | some (q, side) =>
          match inp with
          | none => foldAction side work (M.tm.tr q none (fun i => foldRead (side i) (work i)))
          | some v => match foldDecode v with
            | none => foldHalt
            | some a => foldAction side work
                (M.tm.tr q (some a) (fun i => foldRead (side i) (work i))) }

/-- One-step commutation follows from the action correspondence after transporting
the input read and reading each active folded payload. Halting is absorbing on both
sides; valid embedded symbols always pass the input decoder. -/
private lemma foldCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List Γ} (c : Cfg M.k Γ M.State x) :
    (foldTM M).tm.step (foldCfg c) = foldCfg (M.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [foldCfg, hs, Option.map_none]; rfl
  | some q =>
    have hs' : (foldCfg c).state = some (some (q, fun i => foldSide (c.workTapePos i))) := by
      simp only [foldCfg, hs, Option.map_some]
    rw [hs']
    dsimp only
    rw [foldCfg_input]
    have hw : (fun i => foldRead (foldSide (c.workTapePos i))
        ((foldCfg c).workTapeSymbols i)) = c.workTapeSymbols := by
      funext i
      exact foldRead_tape _ _
    cases hi : c.inputSymbol with
    | none =>
      dsimp only [Option.map, foldTM]
      rw [hw]
      exact foldCfg_apply _ c
    | some a =>
      dsimp only [Option.map, foldTM, foldDecode, foldEmbedding]
      rw [hw]
      exact foldCfg_apply _ c

private lemma foldCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) :
    (foldTM M).tm.step ((foldTM M).tm.initCfg (x.map foldEmbedding)) =
      foldCfg (M.tm.initCfg x) := by
  unfold MultiTapeTM.step
  change (foldStartAction M.tm.q₀ _).apply _ = _
  have hi := foldCfg_input (M.tm.initCfg x)
  change ((foldTM M).tm.initCfg (x.map foldEmbedding)).inputSymbol = _ at hi
  rw [hi, foldStartAction_embed]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [foldInitAction, foldCfg]
  · funext i p
    simp [foldInitAction, foldCfg, foldTape, foldPack, Function.update_apply]
    split_ifs <;> simp_all
  · funext i
    simp [foldInitAction, foldCfg, foldPos]

private lemma foldCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (foldTM M).tm.runFrom ((foldTM M).tm.initCfg (x.map foldEmbedding)) (t + 1) =
      foldCfg (M.tm.runFrom (M.tm.initCfg x) t) := by
  induction t with
  | zero => simpa only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero] using foldCfg_init M x
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, foldCfg_step,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma foldWrite_origin {Γ : Type} (s : Bool) (w : Option (FoldSymbol Γ))
    (a : Option Γ) : (foldUnpack (foldWrite s w a)).1 = (foldUnpack w).1 := by
  simp only [foldWrite, foldUnpack_pack]

private lemma foldMove_nonneg (p : ℤ) (hp : 0 ≤ p) (side : Bool) (d : SignType) :
    0 ≤ p + ((foldMove side (decide (p = 0)) d).1 : ℤ) := by
  by_cases h : p = 0 <;> cases side <;> cases d <;>
    simp [foldMove, h, SignType.cast] <;> omega

/-- After initialization the initial control state is unreachable, all physical
heads are nonnegative, and the origin field is correct at every nonnegative cell.
This invariant quantifies over arbitrary enlarged-alphabet inputs. -/
private def foldSafe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x) : Prop :=
  c.state ≠ some none ∧
    (∀ i, 0 ≤ c.workTapePos i) ∧
      ∀ i p, 0 ≤ p → (foldUnpack (c.workTapes i p)).1 = decide (p = 0)

/-- A translated action preserves origin fields and cannot move left from zero.
The next control state is either halted or a source state, never initialization. -/
private lemma foldAction_safe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x)
    (hc : foldSafe c) (side : Fin k → Bool) (a : Action k Γ S) :
    foldSafe ((foldAction side c.workTapeSymbols a).apply c) := by
  refine ⟨?_, ?_, ?_⟩
  · cases ha : a.state <;> simp [foldAction, Action.apply, ha]
  · intro i
    change 0 ≤ c.workTapePos i +
      ((foldMove (side i) (foldUnpack (c.workTapeSymbols i)).1 (a.workTapes i).2).1 : ℤ)
    rw [show (foldUnpack (c.workTapeSymbols i)).1 = decide (c.workTapePos i = 0)
      from hc.2.2 i _ (hc.2.1 i)]
    exact foldMove_nonneg _ (hc.2.1 i) _ _
  · intro i p hp
    cases hw : (a.workTapes i).1 with
    | none => simpa only [Action.apply, foldAction, hw, Option.map_none] using hc.2.2 i p hp
    | some w =>
      simp only [Action.apply, foldAction, hw, Option.map_some]
      by_cases he : p = c.workTapePos i
      · subst p
        rw [Function.update_self, foldWrite_origin]
        exact hc.2.2 i _ hp
      · rw [Function.update_of_ne he]
        exact hc.2.2 i p hp

private lemma foldHalt_safe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x)
    (hc : foldSafe c) : foldSafe (foldHalt.apply c) := by
  simpa [foldSafe, foldHalt, Action.apply] using hc.2

/-- Every post-initialization transition preserves safety. Valid input reads use
the folding action; a non-image symbol selects a stationary halt. -/
private lemma foldSafe_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List (FoldSymbol Γ)}
    (c : Cfg (foldTM M).k (FoldSymbol Γ) (foldTM M).State x) (hc : foldSafe c) :
    foldSafe ((foldTM M).tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => exact hc
  | some q =>
    cases q with
    | none => exact False.elim (hc.1 hs)
    | some q =>
      rcases q with ⟨q, side⟩
      dsimp only [foldTM]
      cases hi : c.inputSymbol with
      | none => exact foldAction_safe c hc side _
      | some v =>
        dsimp only
        cases hd : foldDecode v with
        | none => exact foldHalt_safe c hc
        | some a => exact foldAction_safe c hc side _

private lemma foldSafe_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List (FoldSymbol Γ)) :
    foldSafe ((foldTM M).tm.step ((foldTM M).tm.initCfg x)) := by
  have hsafe : ∀ (st : Option (foldTM M).State), st ≠ some none →
      foldSafe (({ foldInitAction M.tm.q₀ with state := st }).apply
        ((foldTM M).tm.initCfg x)) := by
    intro st hst
    refine ⟨hst, fun i => by simp [foldInitAction], ?_⟩
    intro i p hp
    by_cases h : p = 0
    · subst p
      simp [foldInitAction, foldUnpack]
    · simp [foldInitAction, foldUnpack, h]
  unfold MultiTapeTM.step
  change foldSafe ((foldStartAction M.tm.q₀ _).apply _)
  unfold foldStartAction
  split
  · exact hsafe _ (by simp)
  · split <;> exact hsafe _ (by simp)

private lemma foldTM_nonnegative {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) : (foldTM M).NonnegativeHeads := by
  intro x t i
  cases t with
  | zero => simp
  | succ t =>
    have hs : ∀ t, foldSafe ((foldTM M).tm.runFrom
        ((foldTM M).tm.step ((foldTM M).tm.initCfg x)) t) := by
      intro t
      induction t with
      | zero => exact foldSafe_init M x
      | succ t ih =>
        rw [MultiTapeTM.runFrom_succ_eq_step']
        exact foldSafe_step M _ ih
    rw [MultiTapeTM.runFrom_succ_eq_step]
    exact (hs t).2.1 i

/-- **Unidirectional tapes suffice** [AB09, Claim 1.8]: a `Γ`-machine computing `f`
within `T` is simulated, with the same number of work tapes and constant-factor
slowdown, by a machine over an enlarged alphabet whose work heads never visit negative
cells.

**Proof sketch.** Fold each tape at the origin along the coordinate
`φ z = if 0 ≤ z then z else -z - 1` (note `φ 0 = φ (-1) = 0`; this is *not* the
absolute value): physical cell `p ≥ 0` holds the two *independent* payloads —
simulated cell `p` and simulated cell `-p - 1`, each possibly blank — over the
enlarged non-blank alphabet `Γ' = Bool × Option Γ × Option Γ`, whose Boolean
component is an origin flag; `e γ = (false, some γ, none)` (injective via its first
payload), and an untouched physical blank decodes as two blanks with no flag. The
simulator's state tracks, per tape, which component the simulated head is in. Because
a transition cannot read a head coordinate, the origin is made *detectable* by a
fresh initialization state whose single action writes `(true, none, none)` at cell
`0` of every work tape simultaneously (one transition, length-independent); every
later write updates only the active payload, preserving the other payload and the
flag. Moves translate directly except at the fold: crossing between simulated cells `0`
and `-1` flips the component *without* issuing a physical move (the physical
coordinate stays `0`); each simulated step costs a constant number of physical steps,
giving `c · (T n + 1)` — [AB09] gets `4T`. Physical head positions are values of `φ`,
hence nonnegative; on enlarged-alphabet inputs containing symbols outside the range
of `e` — where no functional behavior is promised but `NonnegativeHeads` still
quantifies — the simulator halts safely on first contact, preserving nonnegativity
(phase-2 audit, finding 10 and case A14). The folding invariant transfers computation
and halting on embedded inputs.

**Implementation note (epoch 2, batch C).** The private configuration map uses
canonical packing: an untagged pair of blanks is a physical blank. Initialization
costs one step and the subsequent simulation is lockstep, so the displayed constant
can be chosen as one. Safety is proved separately for every enlarged-alphabet input,
including malformed symbols, without using the computation premise. An invalid
first symbol causes halting during the initialization transition itself. -/
theorem nonnegative_heads {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.NonnegativeHeads ∧ M'.k = M.k ∧
        M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) := by
  refine ⟨FoldSymbol Γ, inferInstance, inferInstance, foldEmbedding, foldTM M, 1,
    foldTM_nonnegative M, rfl, ?_⟩
  intro x
  rw [computesInTime_iff]
  dsimp only
  rw [one_mul, foldCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x (f x) (T x.length)).1 (hM x)
  simp only [foldCfg, hs, ho, Option.map_none, and_self]

end Turing.FinTM
