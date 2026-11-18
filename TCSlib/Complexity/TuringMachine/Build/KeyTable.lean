/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.WordArith
import TCSlib.Complexity.TuringMachine.Build.InputRewind

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed tables: lookup and assignment by a key held on another tape

A **keyed table** is a list of entries `(key, value)` of binary words, laid out on one work tape
in the record-table layout of `Build/RecordTable` (`Turing.TableAt`): the header `[true]`, then
for each entry the two fields `true :: key` and `true :: value`, fields separated by one blank,
two blanks before the header and after the last field. The leading `true` of each field keeps
every field nonempty, so the layout is well formed (`Turing.TableWF`) even for empty keys or
values, and a blank pair marks the table's end.

The two rows are the host of a memory: **lookup** copies the value stored under a key, held on
another tape, into a register (the all-`false` word if the key is absent), and **assignment**
overwrites the value stored under a key in place, or appends a new entry. They are the memory of
a word RAM run on a Turing machine (`WordRAM.exists_simulation`), where keys are addresses and
values are words, but they are generic in both.

The record-table rows `Turing.exists_tableFindTM` and `Turing.exists_tableAppendTM` select by a
finite-state predicate and do not read a key from another tape; they are not used here.

## Main definitions

* `Turing.keyFields`, `Turing.keyTableLength`, `Turing.KeyTableAt`: the layout.
* `Turing.keyLookup`, `Turing.keyAssign`: the two operations on lists of entries.
* `Turing.keyTableWrite`: the tapes after laying a keyed table out.

## Main results

* `Turing.exists_keyLookupTM`: lookup, within `O(table + key + value)` steps.
* `Turing.exists_keyAssignTM`: assignment, within the same bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: a RAM's memory kept by a Turing machine as a
  list of address and value pairs, scanned at each access.)
-/

namespace Turing

/-! ## The layout -/

/-- **The fields of a keyed table's entries**: each entry `(k, v)` gives the two fields
`true :: k` and `true :: v`. -/
def keyFields (es : List (List Bool × List Bool)) : List (List (List Bool)) :=
  es.map fun e => [true :: e.1, true :: e.2]

/-- The fields of a keyed table's entries, as an equation. -/
theorem keyFields_def (es : List (List Bool × List Bool)) :
    keyFields es = es.map fun e => [true :: e.1, true :: e.2] := rfl

/-- **The length of a keyed table's layout**: the cells from the header's first to the last
field's last, separators included (the sentinels excluded). -/
def keyTableLength (es : List (List Bool × List Bool)) : ℕ :=
  (joinFields (tableFields [true] (keyFields es))).length

/-- The length of a keyed table's layout, as an equation. -/
theorem keyTableLength_def (es : List (List Bool × List Bool)) :
    keyTableLength es = (joinFields (tableFields [true] (keyFields es))).length := rfl

/-- **A keyed table on a tape**: tape `r` holds the record-table layout of the header `[true]`
and the entries `keyFields es` from the origin `o` (`Turing.TableAt`, with its two blank cells on
either side), and every cell after the layout is blank, so that the table can grow. -/
def KeyTableAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Prop :=
  TableAt d r o [true] (keyFields es) ∧
    ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none

/-- `KeyTableAt`, as an equivalence with its definition. -/
theorem keyTableAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt d r o es ↔ TableAt d r o [true] (keyFields es) ∧
      ∀ q : ℤ, o + (keyTableLength es : ℤ) ≤ q → d.workTapes r q = none :=
  Iff.rfl

/-- **The tapes after laying a keyed table out**: on tape `r`, the cells `[o, o + L)` hold the
layout of `es`, `L = keyTableLength es`; every other cell, of every tape, is unchanged. -/
def keyTableWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (q - o)
    else d.workTapes j q

/-- `keyTableWrite`, as an equation. -/
theorem keyTableWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (o : ℤ) (es : List (List Bool × List Bool)) (j : Fin K) (q : ℤ) :
    keyTableWrite d r o es j q =
      if j = r ∧ o ≤ q ∧ q < o + (keyTableLength es : ℤ)
        then fieldsTape (tableFields [true] (keyFields es)) (q - o)
      else d.workTapes j q :=
  rfl

/-! ## The operations -/

/-- **Lookup**: the value of the first entry whose key is `k`, if any. -/
def keyLookup (es : List (List Bool × List Bool)) (k : List Bool) : Option (List Bool) :=
  (es.find? fun e => e.1 = k).map Prod.snd

/-- Lookup, as an equation. -/
theorem keyLookup_def (es : List (List Bool × List Bool)) (k : List Bool) :
    keyLookup es k = (es.find? fun e => e.1 = k).map Prod.snd := rfl

/-- **Assignment**: if some entry has the key `k`, every such entry's value becomes `v`;
otherwise the entry `(k, v)` is appended. -/
def keyAssign (es : List (List Bool × List Bool)) (k v : List Bool) :
    List (List Bool × List Bool) :=
  if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
  else es ++ [(k, v)]

/-- Assignment, as an equation. -/
theorem keyAssign_def (es : List (List Bool × List Bool)) (k v : List Bool) :
    keyAssign es k v =
      if es.any (fun e => e.1 = k) then es.map fun e => if e.1 = k then (k, v) else e
      else es ++ [(k, v)] := rfl

/-! ## Private marker adaptation -/

/-- Erase the marker under head `r` and advance that head to the payload. -/
private def kt_openMarker {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) : Cfg K Bool S x :=
  { d with
    workTapes := Function.update d.workTapes r
      (Function.update (d.workTapes r) (d.workTapePos r) none)
    workTapePos := Function.update d.workTapePos r (d.workTapePos r + 1) }

/-- Clearing a marked field's marker gives a blank-delimited payload, including when the
payload is empty.

**Proof sketch.** Read the marked word using `Turing.wordAt_iff`. The new left delimiter is
the erased cell; every nonnegative payload offset is the next cell of the marked word.
`Turing.FinTM.bufferTape_eq` and list lookup on a cons identify those cells. -/
private theorem kt_openMarker_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (w : List Bool) (hw : WordAt d r (true :: w)) :
    WordAt (kt_openMarker d r) r w := by
  rw [wordAt_iff] at hw ⊢
  intro p hp hp'
  simp only [kt_openMarker, Function.update_self]
  by_cases hneg : p < 0
  · have heq : p = -1 := by omega
    subst p
    rw [show d.workTapePos r + 1 + -1 = d.workTapePos r by omega,
      Function.update_self, FinTM.bufferTape_left]
  · have hp0 : 0 ≤ p := by omega
    rw [Function.update_of_ne (show d.workTapePos r + 1 + p ≠ d.workTapePos r by omega),
      show d.workTapePos r + 1 + p = d.workTapePos r + (1 + p) by omega,
      hw (1 + p) (by omega) (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; omega)]
    rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos (by omega), if_pos hp0,
      show (1 + p).toNat = p.toNat + 1 by omega, List.getElem?_cons_succ]

/-- Return from a payload head to its marker and restore the marker. -/
private def kt_closeMarker {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) : Cfg K Bool S x :=
  { d with
    workTapes := Function.update d.workTapes r
      (Function.update (d.workTapes r) (d.workTapePos r - 1) (some true))
    workTapePos := Function.update d.workTapePos r (d.workTapePos r - 1) }

/-- Opening and immediately closing a marked field restores the complete configuration.

**Proof sketch.** The head advances and retreats once. Both writes address the old marker
cell; the second replaces its original `some true`. All other tape cells and heads are fixed. -/
private theorem kt_closeMarker_openMarker {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K)
    (hm : d.workTapes r (d.workTapePos r) = some true) :
    kt_closeMarker (kt_openMarker d r) r = d := by
  apply Cfg.ext <;> try rfl
  · funext j q
    by_cases hj : j = r
    · subst j
      simp only [kt_closeMarker, kt_openMarker, Function.update_self, add_sub_cancel_right,
        Function.update_apply]
      split_ifs with hq
      · rw [hq]
        exact hm.symm
      · rfl
    · simp only [kt_closeMarker, kt_openMarker, Function.update_of_ne hj]
  · funext j
    by_cases hj : j = r
    · subst j
      simp only [kt_closeMarker, kt_openMarker, Function.update_self, add_sub_cancel_right]
    · simp only [kt_closeMarker, kt_openMarker, Function.update_of_ne hj]

/-- The catalog has no fixed one-cell delimiter eraser. This two-state leaf performs one
`tapeAction`, then exposes its exit; the table traversal itself uses the phase host. -/
private def kt_cellTM {K : ℕ} (r : Fin K) (wr : Option (Option Bool)) (m : SignType) :
    MultiTapeTM K Bool Bool where
  q₀ := false
  tr := fun b _ _ => if b then inputMoveAction 0 true else tapeAction r 0 wr m true

/-- The complete endpoint of the delimiter leaf, including its unchanged outer frame. -/
private def kt_cellPost {K : ℕ} {x : List Bool} (r : Fin K) (wr : Option (Option Bool))
    (m : SignType) (d : Cfg K Bool Bool x) : Cfg K Bool Bool x :=
  { d with
    state := some true
    workTapes := match wr with
      | none => d.workTapes
      | some b => Function.update d.workTapes r
          (Function.update (d.workTapes r) (d.workTapePos r) b)
    workTapePos := Function.update d.workTapePos r (d.workTapePos r + m) }

/-- The delimiter leaf has the stated one-step endpoint.

**Proof sketch.** Its entry transition is `Turing.tapeAction`. Use
`Turing.step_of_tapeAction_move` when there is no write and
`Turing.step_of_tapeAction_write` otherwise; `Turing.moveInputPos_zero` fixes the input head. -/
private theorem kt_cellTM_run {K : ℕ} {x : List Bool} (r : Fin K)
    (wr : Option (Option Bool)) (m : SignType) (d : Cfg K Bool Bool x)
    (hd : d.state = some false) :
    (kt_cellTM r wr m).runFrom d 1 = kt_cellPost r wr m d := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  cases wr with
  | none =>
    rw [step_of_tapeAction_move (kt_cellTM r none m) d r 0 m hd rfl]
    apply Cfg.ext <;> simp only [kt_cellPost, moveInputPos_zero]
  | some b =>
    rw [step_of_tapeAction_write (kt_cellTM r (some b) m) d r 0 b m hd rfl]
    apply Cfg.ext <;> simp only [kt_cellPost, moveInputPos_zero]

/-- The cell leaf's true control parks forever without changing any physical field. -/
private theorem kt_cellTM_park {K : ℕ} {x : List Bool} (r : Fin K)
    (wr : Option (Option Bool)) (m : SignType) (d : Cfg K Bool Bool x)
    (hd : d.state = some true) (n : ℕ) : (kt_cellTM r wr m).runFrom d n = d := by
  have hfix : (kt_cellTM r wr m).step d = d := by
    rw [step_of_inputMoveAction (kt_cellTM r wr m) d 0 hd rfl]
    refine Cfg.ext hd.symm ?_ rfl rfl rfl
    rw [moveInputPos_zero]
  induction n with
  | zero => rw [MultiTapeTM.runFrom_zero]
  | succ n ih => rw [MultiTapeTM.runFrom_succ_eq_step, hfix, ih]

/-- Package the one-cell leaf with any caller-supplied precondition.

**Proof sketch.** `kt_cellTM_run` supplies the endpoint, and the distinct Boolean entry and
exit give its first-exit cut. `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` supplies the
one-step head envelope. -/
private def kt_cellContract {K : ℕ} {ι : Type} {x : List Bool} (r : Fin K)
    (wr : Option (Option Bool)) (m : SignType) (pre : ι → Cfg K Bool Bool x → Prop) :
    Contract (kt_cellTM r wr m) false {some true} ι x := by
  refine {
    pre := pre
    time := fun _ _ => 1
    post := fun _ d => kt_cellPost r wr m d
    lo := fun _ d j => d.workTapePos j - 1
    hi := fun _ d j => d.workTapePos j + 1
    run := fun _ d hd _ => kt_cellTM_run r wr m d hd
    exit_mem := fun _ _ _ _ => rfl
    cut := ?_
    env := ?_ }
  · intro _ d hd _ u hu
    have heq : u = 0 := by omega
    subst u
    rw [MultiTapeTM.runFrom_zero]
    simpa only [Set.mem_singleton_iff, hd, Option.some.injEq, Bool.false_eq_true] using
      not_false
  · intro _ d _ _ u hu j
    have h := MultiTapeTM.workTapePos_runFrom_mem_Icc (kt_cellTM r wr m) d u j
    have hu' : (u : ℤ) ≤ 1 := by exact_mod_cast hu
    simp only [Finset.mem_Icc] at h ⊢
    constructor <;> omega

/-- The marker-restoration leaf: move left from the payload, then restore `true`. -/
private def kt_closeTM {K : ℕ} (r : Fin K) : MultiTapeTM K Bool (Bool ⊕ Bool) :=
  seamCompTM (kt_cellTM r none .neg) true (kt_cellTM r (some (some true)) 0) false

/-- The restoration leaf's contract is the seam composition of its two cell contracts. -/
private def kt_closeContract {K : ℕ} {x : List Bool} (r : Fin K) :
    Contract (kt_closeTM r) (.inl false)
      (Option.map (Sum.inr : Bool → Bool ⊕ Bool) '' {some true}) Unit x :=
  Contract.seq
    (kt_cellContract r none .neg (fun (_ : Unit) _ => True))
    (kt_cellContract r (some (some true)) 0 (fun (_ : Unit) _ => True))
    (fun _ => ()) (fun _ _ _ _ => True.intro)

/-- Marker restoration takes three steps, has no data precondition, and changes exactly
the marker and its head.

**Proof sketch.** Read the sequential contract through `Turing.Contract.seq_pre`,
`Turing.Contract.seq_time` and `Turing.Contract.seq_post`. State relabelings keep all tape
fields; the first leaf moves left and the second writes at that cell. -/
private theorem kt_closeContract_spec {K : ℕ} {x : List Bool} (r : Fin K)
    (d : Cfg K Bool (Bool ⊕ Bool) x) :
    (kt_closeContract r).pre () d ∧ (kt_closeContract r).time () d = 3 ∧
      (kt_closeContract r).post () d =
        { kt_closeMarker d r with state := some (.inr true) } := by
  have hneg : (↑SignType.neg : ℤ) = -1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [kt_closeContract, Contract.seq_pre]
    trivial
  · rw [kt_closeContract, Contract.seq_time]
    rfl
  · rw [kt_closeContract, Contract.seq_post]
    apply Cfg.ext
    · simp only [kt_cellContract, kt_cellPost, Cfg.mapState_state, Option.map_some]
    · simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_inputPos]
    · funext j q
      by_cases hj : j = r
      · subst j
        simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Function.update_self, hneg, ← sub_eq_add_neg,
          Function.update_apply]
      · simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Function.update_of_ne hj]
    · funext j
      by_cases hj : j = r
      · subst j
        simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_workTapePos,
          Function.update_self, SignType.coe_zero, hneg, add_zero]
        omega
      · simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_workTapePos,
          Function.update_of_ne hj]
    · simp only [kt_cellContract, kt_cellPost, kt_closeMarker, Cfg.mapState_output]

/-- The payload phase uses the row's state type. Each restoration phase remembers the row's
exit state and uses the two-cell restoration controller. -/
private def kt_payloadControl (S : Type) : Option S → Type
  | none => S
  | some _ => Bool ⊕ Bool

/-- Payload and restoration routines for the existing phase host. -/
private def kt_payloadParts {K : ℕ} {S : Type} (r : Fin K) (M : MultiTapeTM K Bool S) :
    (p : Option S) → MultiTapeTM K Bool (kt_payloadControl S p)
  | none => M
  | some _ => kt_closeTM r

/-- Redirect each live row exit into its own marker-restoration phase. -/
private def kt_payloadRedirect {S : Type} (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] :
    (p : Option S) → kt_payloadControl S p → Option (Σ p, kt_payloadControl S p)
  | none, s => if some s ∈ X then some ⟨some s, .inl false⟩ else none
  | some _, _ => none

/-- Run a row at the payload and restore the marker at its exit, using `phaseHostTM`. -/
private def kt_payloadTM {K : ℕ} {S : Type} (r : Fin K) (M : MultiTapeTM K Bool S)
    (entry : S) (X : Set (Option S)) [DecidablePred fun s => some s ∈ X] :
    MultiTapeTM K Bool (Σ p, kt_payloadControl S p) :=
  phaseHostTM (kt_payloadParts r M) ⟨none, entry⟩ (kt_payloadRedirect X)

/-- Every restoration phase exposes the same local exit. Its index retains the row's verdict. -/
private def kt_payloadExits (S : Type) : Set (Option (Σ p, kt_payloadControl S p)) :=
  { q | ∃ s : S, q = some ⟨some s, .inr true⟩ }

/-- The adapter follows the row through its first exit, dispatches once, then follows the
restoration leaf. The exit value remains the restoration phase's index.

**Proof sketch.** The row contract supplies its endpoint and excludes redirects before it.
`Turing.phaseHostTM_run` gives the row segment and dispatch. The restoration phase has no
redirect, so `Turing.phaseHostTM_run_le` gives its whole segment. Concatenate with
`Turing.MultiTapeTM.runFrom_add` and `Turing.Cfg.mapState_mapState`. -/
private theorem kt_payloadTrace {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X)
    (i : ι) (d : Cfg K Bool S x) (hd : d.state = some entry) (hp : C.pre i d) :
    ∃ s : S, (C.post i d).state = some s ∧
      (∀ u ≤ C.time i d,
        (kt_payloadTM r M entry X).runFrom (d.mapState (Sigma.mk none)) u =
          (M.runFrom d u).mapState (Sigma.mk none)) ∧
      (∀ v ≤ 3,
        (kt_payloadTM r M entry X).runFrom (d.mapState (Sigma.mk none))
            (C.time i d + 1 + v) =
          ((kt_closeTM r).runFrom ((C.post i d).mapState fun _ => .inl false) v).mapState
            (Sigma.mk (some s))) := by
  have hne : (C.post i d).state ≠ none := by
    intro he
    have hx := C.exit_mem i d hd hp
    rw [he] at hx
    exact hnone hx
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hne
  have hsX : some s ∈ X := by rw [← hs]; exact C.exit_mem i d hd hp
  have hguard : ∀ u < C.time i d, ∀ q,
      (M.runFrom d u).state = some q → kt_payloadRedirect X none q = none := by
    intro u hu q hq
    have hqX : some q ∉ X := by
      intro hx
      apply C.cut i d hd hp u hu
      rw [hq]
      exact hx
    exact if_neg hqX
  have hrow := phaseHostTM_run (kt_payloadParts r M) ⟨none, entry⟩
    (kt_payloadRedirect X) none d (C.post i d) (C.time i d) (C.run i d hd hp) s hs
    ⟨some s, .inl false⟩ (if_pos hsX) hguard
  have hlast := phaseHostTM_run_le (kt_payloadParts r M) ⟨none, entry⟩
    (kt_payloadRedirect X) (some s) ((C.post i d).mapState fun _ => .inl false) 3
    (fun _ _ _ _ => rfl)
  refine ⟨s, hs, hrow.1, ?_⟩
  intro v hv
  rw [MultiTapeTM.runFrom_add, hrow.2]
  simpa only [Cfg.mapState_mapState] using hlast v hv

/-- The row endpoint after restoring the marker, tagged by the row's retained exit state. -/
private def kt_payloadPost {K : ℕ} {S ι : Type} {x : List Bool}
    {M : MultiTapeTM K Bool S} {entry : S} {X : Set (Option S)}
    (r : Fin K) (C : Contract M entry X ι x) (i : ι) (d : Cfg K Bool S x) :
    Cfg K Bool (Σ p, kt_payloadControl S p) x :=
  let e := C.post i d
  let z := (kt_closeContract r).post () (e.mapState fun _ => .inl false)
  ⟨e.state.map (fun s => ⟨some s, .inr true⟩), z.inputPos, z.workTapes, z.workTapePos, z.output⟩

/-- A payload row followed by marker restoration has four extra steps and cannot expose a
restoration exit earlier.

**Proof sketch.** `kt_payloadTrace` splits the run into the original row and the restoration
leaf. `kt_closeContract_spec` fixes the latter's time to three. Before dispatch the phase
indices exclude every restoration exit; afterwards the leaf's first-exit cut excludes it. -/
private theorem kt_payload_run {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X)
    (i : ι) (d : Cfg K Bool S x) (hd : d.state = some entry) (hp : C.pre i d) :
    (kt_payloadTM r M entry X).runFrom (d.mapState (Sigma.mk none)) (C.time i d + 4) =
        kt_payloadPost r C i d ∧
      ∀ u < C.time i d + 4,
        ((kt_payloadTM r M entry X).runFrom (d.mapState (Sigma.mk none)) u).state ∉
          kt_payloadExits S := by
  obtain ⟨s, hs, hfirst, hlast⟩ := kt_payloadTrace r M entry X C hnone i d hd hp
  let e : Cfg K Bool (Bool ⊕ Bool) x := (C.post i d).mapState fun _ => .inl false
  have he : e.state = some (.inl false) := by
    rw [Cfg.mapState_state, hs, Option.map_some]
  have hspec := kt_closeContract_spec r e
  have hrun := (kt_closeContract r).run () e he hspec.1
  rw [hspec.2.1] at hrun
  have hcut : ∀ u < 3, ((kt_closeTM r).runFrom e u).state ≠ some (.inr true) := by
    intro u hu h
    apply (kt_closeContract r).cut () e he hspec.1 u (by rw [hspec.2.1]; exact hu)
    simpa only [Set.image_singleton, Option.map_some, Set.mem_singleton_iff] using h
  refine ⟨?_, ?_⟩
  · have h := hlast 3 le_rfl
    rw [hrun] at h
    rw [show C.time i d + 1 + 3 = C.time i d + 4 by omega] at h
    refine h.trans ?_
    apply Cfg.ext
    · rw [Cfg.mapState_state, hspec.2.2]
      simp only [kt_payloadPost, hs, Option.map_some]
    · simp only [kt_payloadPost, e, Cfg.mapState_inputPos]
    · funext j q
      simp only [kt_payloadPost, e, Cfg.mapState_workTapes]
    · funext j
      simp only [kt_payloadPost, e, Cfg.mapState_workTapePos]
    · simp only [kt_payloadPost, e, Cfg.mapState_output]
  · intro u hu
    by_cases hle : u ≤ C.time i d
    · rw [hfirst u hle]
      rintro ⟨q, hq⟩
      exact Cfg.mapState_sigma_state_ne (Ph := kt_payloadControl S) none ⟨some q, .inr true⟩
        (by intro h; cases h) (M.runFrom d u) hq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C.time i d + 1 + v :=
        ⟨u - (C.time i d + 1), by omega⟩
      rw [hlast v (by omega)]
      rintro ⟨q, hq⟩
      rw [Cfg.mapState_state] at hq
      obtain ⟨a, ha, hindex⟩ := Option.map_eq_some_iff.mp hq
      have hsq : s = q := Option.some.inj (congrArg Sigma.fst hindex)
      subst q
      have haExit : a = .inr true := sigma_mk_injective hindex
      exact hcut v (by omega) (ha.trans (congrArg some haExit))

/-- The payload adapter's run and cut from a configuration already tagged at its entry. -/
private theorem kt_payload_run_of_start {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X)
    (i : ι) (d : Cfg K Bool (Σ p, kt_payloadControl S p) x)
    (hd : d.state = some ⟨none, entry⟩) (hp : C.pre i (d.mapState fun _ => entry)) :
    (kt_payloadTM r M entry X).runFrom d (C.time i (d.mapState fun _ => entry) + 4) =
        kt_payloadPost r C i (d.mapState fun _ => entry) ∧
      ∀ u < C.time i (d.mapState fun _ => entry) + 4,
        ((kt_payloadTM r M entry X).runFrom d u).state ∉ kt_payloadExits S := by
  have hd' : (d.mapState fun _ => entry).state = some entry := by
    rw [Cfg.mapState_state, hd, Option.map_some]
  have hstart : (d.mapState fun _ => entry).mapState (Sigma.mk none) = d := by
    rw [Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields d _ d (by rw [hd]; rfl) rfl rfl rfl rfl
  have h := kt_payload_run r M entry X C hnone i _ hd' hp
  rwa [hstart] at h

/-- Turn a row contract into the payload-and-restoration contract.

**Proof sketch.** `kt_payload_run_of_start` supplies the exact run and first-exit cut.
`kt_payloadTrace` supplies the retained live exit. The general head-displacement bound gives
the time-derived envelope for the whole adapter. -/
private def kt_payloadContract {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X) :
    Contract (kt_payloadTM r M entry X) ⟨none, entry⟩ (kt_payloadExits S) ι x := by
  refine {
    pre := fun i d => C.pre i (d.mapState fun _ => entry)
    time := fun i d => C.time i (d.mapState fun _ => entry) + 4
    post := fun i d => kt_payloadPost r C i (d.mapState fun _ => entry)
    lo := fun i d j => d.workTapePos j - (C.time i (d.mapState fun _ => entry) + 4)
    hi := fun i d j => d.workTapePos j + (C.time i (d.mapState fun _ => entry) + 4)
    run := fun i d hd hp => (kt_payload_run_of_start r M entry X C hnone i d hd hp).1
    cut := fun i d hd hp => (kt_payload_run_of_start r M entry X C hnone i d hd hp).2
    exit_mem := ?_
    env := ?_ }
  · intro i d hd hp
    have hd' : (d.mapState fun _ => entry).state = some entry := by
      rw [Cfg.mapState_state, hd, Option.map_some]
    obtain ⟨s, hs, -, -⟩ := kt_payloadTrace r M entry X C hnone i _ hd' hp
    exact ⟨s, by simp only [kt_payloadPost, hs, Option.map_some]⟩
  · intro i d _ _ u hu j
    have h := MultiTapeTM.workTapePos_runFrom_mem_Icc (kt_payloadTM r M entry X) d u j
    have hu' : (u : ℤ) ≤ ((C.time i (d.mapState fun _ => entry) + 4 : ℕ) : ℤ) := by
      exact_mod_cast hu
    simp only [Finset.mem_Icc] at h ⊢
    constructor <;> omega

/-- The shared marker adapter: clear and advance once, dispatch into the payload adapter,
run the row, then restore the marker. -/
private def kt_markerTM {K : ℕ} {S : Type} (r : Fin K) (M : MultiTapeTM K Bool S)
    (entry : S) (X : Set (Option S)) [DecidablePred fun s => some s ∈ X] :
    MultiTapeTM K Bool (Bool ⊕ (Σ p, kt_payloadControl S p)) :=
  seamCompTM (kt_cellTM r (some none) .pos) true (kt_payloadTM r M entry X) ⟨none, entry⟩

/-- The private marker contract transformer, shared by field comparison and value copying.
Its precondition is the supplied row's precondition after the marker-clear step.

**Proof sketch.** Use `Turing.Contract.seq` to join the marker-clear cell contract to
`kt_payloadContract`. The cell contract is indexed by the caller's data, so its precondition
is exactly the payload contract's required linked precondition. -/
private def kt_markerContract {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X) :
    Contract (kt_markerTM r M entry X) (.inl false)
      (Option.map Sum.inr '' kt_payloadExits S) ι x :=
  Contract.seq
    (kt_cellContract r (some none) .pos (fun i d =>
      (kt_payloadContract r M entry X C hnone).pre i
        ((kt_cellPost r (some none) .pos d).mapState fun _ => ⟨none, entry⟩)))
    (kt_payloadContract r M entry X C hnone) id (fun _ _ _ hp => hp)

/-- The marker-clear leaf prepares exactly `kt_openMarker`, independently of state tags.

**Proof sketch.** Compare the five configuration fields through the published state-renaming
equations. The leaf writes the same blank marker and advances by one; a live source gives the
same relabelled row entry on both sides. -/
private theorem kt_markerRowStart {K : ℕ} {S U : Type} {x : List Bool}
    (r : Fin K) (entry : S) (d : Cfg K Bool U x) (hd : d.state.isSome) :
    (kt_cellPost r (some none) .pos (d.mapState fun _ => false)).mapState (fun _ => entry) =
      (kt_openMarker d r).mapState (fun _ => entry) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hd
  have hpos : (↑SignType.pos : ℤ) = 1 := rfl
  apply Cfg.ext
  · simp only [kt_cellPost, kt_openMarker, Cfg.mapState_state, hq, Option.map_some]
  · simp only [kt_cellPost, kt_openMarker, Cfg.mapState_inputPos]
  · funext j z
    by_cases hj : j = r
    · subst j
      simp only [kt_cellPost, kt_openMarker, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_self, Function.update_apply]
    · simp only [kt_cellPost, kt_openMarker, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_of_ne hj]
  · funext j
    simp only [kt_cellPost, kt_openMarker, Cfg.mapState_workTapePos, Function.update_apply, hpos]
  · simp only [kt_cellPost, kt_openMarker, Cfg.mapState_output]

/-- The marker adapter requires the original row's precondition on the opened payload and
adds exactly six steps.

**Proof sketch.** Read the outer seam's precondition and time through
`Turing.Contract.seq_pre` and `Turing.Contract.seq_time`. Collapse the two state relabelings
and use `kt_markerRowStart`; the clear leaf, two dispatches and restoration add six steps. -/
private theorem kt_markerContract_pre_time {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X)
    (i : ι) (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl S p)) x)
    (hd : d.state = some (.inl false)) :
    ((kt_markerContract r M entry X C hnone).pre i d ↔
      C.pre i ((kt_openMarker d r).mapState fun _ => entry)) ∧
    (kt_markerContract r M entry X C hnone).time i d =
      C.time i ((kt_openMarker d r).mapState fun _ => entry) + 6 := by
  have hd' : d.state.isSome := by rw [hd]; rfl
  constructor
  · rw [kt_markerContract, Contract.seq_pre]
    change C.pre i (((kt_cellPost r (some none) .pos (d.mapState fun _ => false)).mapState
        fun _ => (⟨none, entry⟩ : Σ p, kt_payloadControl S p)).mapState fun _ => entry) ↔ _
    rw [Cfg.mapState_mapState]
    change C.pre i ((kt_cellPost r (some none) .pos (d.mapState fun _ => false)).mapState
        fun _ => entry) ↔ _
    rw [kt_markerRowStart r entry d hd']
  · rw [kt_markerContract, Contract.seq_time]
    change 1 + 1 + (C.time i (((kt_cellPost r (some none) .pos
      (d.mapState fun _ => false)).mapState
      fun _ => (⟨none, entry⟩ : Σ p, kt_payloadControl S p)).mapState fun _ => entry) + 4) = _
    rw [Cfg.mapState_mapState]
    change 1 + 1 + (C.time i ((kt_cellPost r (some none) .pos
      (d.mapState fun _ => false)).mapState fun _ => entry) + 4) = _
    rw [kt_markerRowStart r entry d hd']
    omega

/-- The framed endpoint of a marker-adapted row: restore its marker, retreat that head,
and retain its exit value in the adapter's control. -/
private def kt_markerPost {K : ℕ} {S : Type} {x : List Bool}
    (r : Fin K) (e : Cfg K Bool S x) :
    Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl S p)) x :=
  let z := kt_closeMarker e r
  ⟨e.state.map (fun s => .inr ⟨some s, .inr true⟩), z.inputPos, z.workTapes,
    z.workTapePos, z.output⟩

/-- The restored payload endpoint has exactly the marker adapter's framed endpoint.

**Proof sketch.** `kt_closeContract_spec` identifies the restoration leaf's endpoint.
Read the state relabelings through their field equations; restoration changes the marker
and its head, and keeps every other field of the supplied row's endpoint. -/
private theorem kt_payloadPost_markerPost {K : ℕ} {S ι : Type} {x : List Bool}
    {M : MultiTapeTM K Bool S} {entry : S} {X : Set (Option S)}
    (r : Fin K) (C : Contract M entry X ι x) (i : ι) (d : Cfg K Bool S x) :
    (kt_payloadPost r C i d).mapState Sum.inr = kt_markerPost r (C.post i d) := by
  have hspec := (kt_closeContract_spec r
    ((C.post i d).mapState fun _ => .inl false)).2.2
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    simp only [kt_payloadPost, kt_markerPost, Option.map_map]
    rfl
  · rw [Cfg.mapState_inputPos]
    change ((kt_closeContract r).post ()
      ((C.post i d).mapState fun _ => .inl false)).inputPos = (C.post i d).inputPos
    rw [hspec]
    simp only [kt_closeMarker, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    change ((kt_closeContract r).post ()
      ((C.post i d).mapState fun _ => .inl false)).workTapes j q =
        (kt_closeMarker (C.post i d) r).workTapes j q
    rw [hspec]
    by_cases hj : j = r
    · subst j
      simp only [kt_closeMarker, Function.update_self, Function.update_apply,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    · simp only [kt_closeMarker, Function.update_of_ne hj, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    change ((kt_closeContract r).post ()
      ((C.post i d).mapState fun _ => .inl false)).workTapePos j =
        (kt_closeMarker (C.post i d) r).workTapePos j
    rw [hspec]
    simp only [kt_closeMarker, Function.update_apply, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output]
    change ((kt_closeContract r).post ()
      ((C.post i d).mapState fun _ => .inl false)).output = (C.post i d).output
    rw [hspec]
    simp only [kt_closeMarker, Cfg.mapState_output]

/-- The shared contract's endpoint is the supplied row's endpoint with its marker restored.

**Proof sketch.** Read `Turing.Contract.seq_post` and collapse its state relabelings.
`kt_markerRowStart` identifies the row start, and `kt_payloadPost_markerPost` identifies
the complete restored endpoint. -/
private theorem kt_markerContract_post {K : ℕ} {S ι : Type} {x : List Bool}
    (r : Fin K) (M : MultiTapeTM K Bool S) (entry : S) (X : Set (Option S))
    [DecidablePred fun s => some s ∈ X] (C : Contract M entry X ι x) (hnone : none ∉ X)
    (i : ι) (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl S p)) x)
    (hd : d.state = some (.inl false)) :
    (kt_markerContract r M entry X C hnone).post i d =
      kt_markerPost r (C.post i ((kt_openMarker d r).mapState fun _ => entry)) := by
  have hd' : d.state.isSome := by rw [hd]; rfl
  rw [kt_markerContract, Contract.seq_post]
  change (kt_payloadPost r C i (((kt_cellPost r (some none) .pos
    (d.mapState fun _ => false)).mapState
    fun _ => (⟨none, entry⟩ : Σ p, kt_payloadControl S p)).mapState fun _ => entry)).mapState
      Sum.inr = _
  rw [Cfg.mapState_mapState]
  change (kt_payloadPost r C i ((kt_cellPost r (some none) .pos
    (d.mapState fun _ => false)).mapState fun _ => entry)).mapState Sum.inr = _
  rw [kt_markerRowStart r entry d hd']
  exact kt_payloadPost_markerPost r C i _

/-- The adapter has finitely many controls whenever its supplied row does. -/
private instance kt_payloadControl_fintype {S : Type} [Fintype S] (p : Option S) :
    Fintype (kt_payloadControl S p) := by
  cases p <;> dsimp only [kt_payloadControl] <;> infer_instance

/-- Compare a marked field on `r` with the query word on `s` through the shared adapter. -/
private noncomputable def kt_compareTM {K : ℕ} (r s : Fin K) :
    MultiTapeTM K Bool (Bool ⊕ (Σ p, kt_payloadControl FlagPhase p)) := by
  classical
  exact kt_markerTM r (compareTM K r s) .run (Set.range fun b => some (FlagPhase.done b))

/-- The marked comparison contract is the catalog's framed comparison under the adapter. -/
private noncomputable def kt_compareContract {K : ℕ} {x : List Bool} (r s : Fin K)
    (hne : r ≠ s) :
    Contract (kt_compareTM r s) (.inl false)
      (Option.map Sum.inr '' kt_payloadExits FlagPhase) (List Bool × List Bool) x := by
  classical
  exact kt_markerContract r (compareTM K r s) .run _ (compareTM_contract r s hne x)
    (by rintro ⟨b, h⟩; cases h)

/-- Copy through the shared marker adapter. The marked field can be either source or
destination; the catalog copy contract reads only its source delimiter. -/
private noncomputable def kt_copyTM {K : ℕ} (r src dst : Fin K) :
    MultiTapeTM K Bool (Bool ⊕ (Σ p, kt_payloadControl SweepPhase p)) := by
  classical
  exact kt_markerTM r (copyTM K src dst) .sweep {some SweepPhase.done}

/-- The marked copy contract is the catalog's framed copy under the same adapter. -/
private noncomputable def kt_copyContract {K : ℕ} {x : List Bool} (r src dst : Fin K)
    (hne : src ≠ dst) :
    Contract (kt_copyTM r src dst) (.inl false)
      (Option.map Sum.inr '' kt_payloadExits SweepPhase) (List Bool) x := by
  classical
  exact kt_markerContract r (copyTM K src dst) .sweep {some SweepPhase.done}
    (copyTM_contract src dst hne x) (by intro h; cases h)

/-- State relabeling preserves a delimited word at any work head. -/
private theorem kt_wordAt_mapState {K : ℕ} {S U : Type} {x : List Bool}
    (d : Cfg K Bool S x) (f : S → U) (r : Fin K) (w : List Bool) (hw : WordAt d r w) :
    WordAt (d.mapState f) r w := by
  rw [wordAt_iff] at hw ⊢
  intro p hp hp'
  rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapes]
  exact hw p hp hp'

/-- Opening one field preserves a word delimited on a different tape. -/
private theorem kt_openMarker_word_other {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r s : Fin K) (hne : s ≠ r) (w : List Bool) (hw : WordAt d s w) :
    WordAt (kt_openMarker d r) s w := by
  rw [wordAt_iff] at hw ⊢
  intro p hp hp'
  simpa only [kt_openMarker, Function.update_of_ne hne] using hw p hp hp'

/-- Marked comparison is admissible for a marked key and an ordinary query, and takes
`2 * compareStop u v + 8` steps.

**Proof sketch.** `kt_openMarker_word` supplies the first delimiter and
`kt_openMarker_word_other` preserves the query. State relabeling preserves both words.
Apply `kt_markerContract_pre_time` to the catalog's comparison contract and read its time. -/
private theorem kt_compareContract_pre_time {K : ℕ} {x : List Bool} (r s : Fin K)
    (hne : r ≠ s) (u v : List Bool)
    (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl FlagPhase p)) x)
    (hd : d.state = some (.inl false)) (hu : WordAt d r (true :: u)) (hv : WordAt d s v) :
    (kt_compareContract r s hne).pre (u, v) d ∧
      (kt_compareContract r s hne).time (u, v) d = 2 * compareStop u v + 8 := by
  classical
  have hbase := kt_markerContract_pre_time r (compareTM K r s) .run
    (Set.range fun b => some (FlagPhase.done b)) (compareTM_contract r s hne x)
    (by rintro ⟨b, h⟩; cases h) (u, v) d hd
  have hpre : (compareTM_contract r s hne x).pre (u, v)
      ((kt_openMarker d r).mapState fun _ => FlagPhase.run) := by
    rw [compareTM_contract_pre]
    exact ⟨(wordAt_iff _ _ _).mp (kt_wordAt_mapState _ _ r u (kt_openMarker_word d r u hu)),
      (wordAt_iff _ _ _).mp
        (kt_wordAt_mapState _ _ s v (kt_openMarker_word_other d r s hne.symm v hv))⟩
  refine ⟨hbase.1.mpr hpre, ?_⟩
  calc
    _ = (compareTM_contract r s hne x).time (u, v)
        ((kt_openMarker d r).mapState fun _ => FlagPhase.run) + 6 := hbase.2
    _ = 2 * compareStop u v + 8 := by rw [compareTM_contract_time]

/-- A row that changes only its state inside the marker adapter restores every tape cell,
head, input position and output of the original configuration.

**Proof sketch.** `kt_closeMarker_openMarker` restores the original physical configuration.
State relabeling and state replacement affect none of its physical fields. Read those fields
through the relabeling equations and retain the supplied exit as the adapter's exit tag. -/
private theorem kt_markerPost_openMarker {K : ℕ} {S U : Type} {x : List Bool}
    (r : Fin K) (d : Cfg K Bool U x) (entry q : S)
    (hm : d.workTapes r (d.workTapePos r) = some true) :
    kt_markerPost r { (kt_openMarker d r).mapState (fun _ => entry) with state := some q } =
      { d with state := some (.inr ⟨some q, .inr true⟩) } := by
  let e : Cfg K Bool S x :=
    { (kt_openMarker d r).mapState (fun _ => entry) with state := some q }
  have hrestore := kt_closeMarker_openMarker d r hm
  apply Cfg.ext
  · simp only [kt_markerPost, Option.map_some]
  · simp only [kt_markerPost, kt_closeMarker, kt_openMarker, Cfg.mapState_inputPos]
  · funext j z
    change (kt_closeMarker e r).workTapes j z = d.workTapes j z
    have h := congrArg (fun c : Cfg K Bool U x => c.workTapes j z) hrestore
    refine Eq.trans ?_ h
    by_cases hj : j = r
    · subst j
      simp only [e, kt_closeMarker, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_self, Function.update_apply]
    · simp only [e, kt_closeMarker, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
        Function.update_of_ne hj]
  · funext j
    change (kt_closeMarker e r).workTapePos j = d.workTapePos j
    have h := congrArg (fun c : Cfg K Bool U x => c.workTapePos j) hrestore
    refine Eq.trans ?_ h
    simp only [e, kt_closeMarker, Cfg.mapState_workTapePos, Function.update_apply]
  · simp only [kt_markerPost, kt_closeMarker, kt_openMarker, Cfg.mapState_output]

/-- Marked comparison returns its Boolean verdict and restores the original configuration's
entire physical frame. -/
private theorem kt_compareContract_post {K : ℕ} {x : List Bool} (r s : Fin K)
    (hne : r ≠ s) (u v : List Bool)
    (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl FlagPhase p)) x)
    (hd : d.state = some (.inl false))
    (hm : d.workTapes r (d.workTapePos r) = some true) :
    (kt_compareContract r s hne).post (u, v) d =
      { d with state := some (.inr ⟨some (.done (decide (u = v))), .inr true⟩) } := by
  classical
  have h := kt_markerContract_post r (compareTM K r s) .run
    (Set.range fun b => some (FlagPhase.done b)) (compareTM_contract r s hne x)
    (by rintro ⟨b, h⟩; cases h) (u, v) d hd
  rw [compareTM_contract_post] at h
  exact h.trans (kt_markerPost_openMarker r d FlagPhase.run (.done (decide (u = v))) hm)

/-- Marked copying is admissible when the opened source is delimited, and takes
`2 * w.length + 8` steps. This covers copying out of and into a table field.

**Proof sketch.** State relabeling preserves the opened source word. Apply
`kt_markerContract_pre_time` to `Turing.copyTM_contract`, and read its source-word
precondition and its two-sweep time through the published contract equations. -/
private theorem kt_copyContract_pre_time {K : ℕ} {x : List Bool} (r src dst : Fin K)
    (hne : src ≠ dst) (w : List Bool)
    (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl SweepPhase p)) x)
    (hd : d.state = some (.inl false)) (hw : WordAt (kt_openMarker d r) src w) :
    (kt_copyContract r src dst hne).pre w d ∧
      (kt_copyContract r src dst hne).time w d = 2 * w.length + 8 := by
  classical
  have hbase := kt_markerContract_pre_time r (copyTM K src dst) .sweep
    {some SweepPhase.done} (copyTM_contract src dst hne x) (by intro h; cases h) w d hd
  have hpre : (copyTM_contract src dst hne x).pre w
      ((kt_openMarker d r).mapState fun _ => SweepPhase.sweep) := by
    rw [copyTM_contract_pre]
    exact (wordAt_iff _ _ _).mp (kt_wordAt_mapState _ _ src w hw)
  refine ⟨hbase.1.mpr hpre, ?_⟩
  calc
    _ = (copyTM_contract src dst hne x).time w
        ((kt_openMarker d r).mapState fun _ => SweepPhase.sweep) + 6 := hbase.2
    _ = 2 * w.length + 8 := by rw [copyTM_contract_time]

/-- The catalog copy endpoint is exactly the word overwrite used by the keyed-table rows. -/
private theorem kt_copy_row_post {K : ℕ} {x : List Bool} (src dst : Fin K)
    (hne : src ≠ dst) (w : List Bool) (d : Cfg K Bool SweepPhase x) :
    (copyTM_contract src dst hne x).post w d =
      { d with state := some .done, workTapes := wordWrite d dst w } := by
  rw [copyTM_contract_post]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [sweepPost_state]
  · rw [sweepPost_inputPos]
  · funext j q
    rw [sweepPost_workTapes]
    change (if j = dst ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
        FinTM.bufferTape w (q - d.workTapePos j) else d.workTapes j q) = wordWrite d dst w j q
    rw [wordWrite_apply]
  · funext j
    rw [sweepPost_workTapePos]
  · rw [sweepPost_output]

/-- The payload overwrite of an adapted copy. Only the marked tape's payload head is
advanced, so this describes both copy directions and appending into the blank tail. -/
private def kt_markerWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x)
    (r dst : Fin K) (w : List Bool) : Fin K → ℤ → Option Bool :=
  wordWrite { d with workTapePos := Function.update d.workTapePos r (d.workTapePos r + 1) } dst w

/-- An adapted copy restores the marker and every head and overwrites exactly its payload
or the ordinary destination word, according to the copy direction.

**Proof sketch.** `kt_markerContract_post` exposes the copied payload and
`kt_copy_row_post` identifies its overwrite. Opening advances only the marked head.
The payload interval excludes the marker, which closing restores to its original true bit;
all other cells agree with `kt_markerWrite`. -/
private theorem kt_copyContract_post {K : ℕ} {x : List Bool} (r src dst : Fin K)
    (hne : src ≠ dst) (w : List Bool)
    (d : Cfg K Bool (Bool ⊕ (Σ p, kt_payloadControl SweepPhase p)) x)
    (hd : d.state = some (.inl false))
    (hm : d.workTapes r (d.workTapePos r) = some true) :
    (kt_copyContract r src dst hne).post w d =
      { d with
        state := some (.inr ⟨some SweepPhase.done, .inr true⟩)
        workTapes := kt_markerWrite d r dst w } := by
  classical
  have h := kt_markerContract_post r (copyTM K src dst) .sweep {some SweepPhase.done}
    (copyTM_contract src dst hne x) (by intro hn; cases hn) w d hd
  rw [kt_copy_row_post] at h
  refine h.trans ?_
  apply Cfg.ext
  · simp only [kt_markerPost, Option.map_some]
  · simp only [kt_markerPost, kt_closeMarker, Cfg.mapState_inputPos, kt_openMarker]
  · funext j q
    change (kt_closeMarker
      { (kt_openMarker d r).mapState (fun _ => SweepPhase.sweep) with
        state := some SweepPhase.done
        workTapes := wordWrite ((kt_openMarker d r).mapState fun _ => SweepPhase.sweep) dst w }
        r).workTapes j q = kt_markerWrite d r dst w j q
    by_cases hj : j = r
    · subst j
      simp only [kt_closeMarker, Cfg.mapState_workTapePos, kt_openMarker,
        Function.update_self, add_sub_cancel_right]
      by_cases hq : q = d.workTapePos r
      · subst q
        simp only [Function.update_self, kt_markerWrite, wordWrite_apply,
          show ¬d.workTapePos r + 1 ≤ d.workTapePos r by omega,
          and_false, false_and, if_false, hm]
      · simp only [kt_markerWrite, wordWrite_apply, Cfg.mapState_workTapes,
          Cfg.mapState_workTapePos, Function.update_self, Function.update_of_ne hq]
    · simp only [kt_closeMarker, Function.update_of_ne hj, kt_markerWrite, wordWrite_apply,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, kt_openMarker]
  · funext j
    by_cases hj : j = r
    · subst j
      simp only [kt_markerPost, kt_closeMarker, Cfg.mapState_workTapePos, kt_openMarker,
        Function.update_self, add_sub_cancel_right]
    · simp only [kt_markerPost, kt_closeMarker, Cfg.mapState_workTapePos, kt_openMarker,
        Function.update_of_ne hj]
  · simp only [kt_markerPost, kt_closeMarker, Cfg.mapState_output, kt_openMarker]

/-- If the destination is not marked, the adapted overwrite is the ordinary word overwrite. -/
private theorem kt_markerWrite_other {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r dst : Fin K) (hne : dst ≠ r) (w : List Bool) :
    kt_markerWrite d r dst w = wordWrite d dst w := by
  funext j q
  by_cases hj : j = dst
  · subst j
    simp only [kt_markerWrite, wordWrite_apply, Function.update_of_ne hne]
  · simp only [kt_markerWrite, wordWrite_apply, hj, false_and, if_false]

/-- A marked word exposes its leading true bit at the current head. -/
private theorem kt_wordAt_marker {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (w : List Bool) (hw : WordAt d r (true :: w)) :
    d.workTapes r (d.workTapePos r) = some true := by
  have h := (wordAt_iff _ _ _).mp hw 0 (by omega) (by exact_mod_cast Nat.zero_le (true :: w).length)
  simpa only [add_zero, FinTM.bufferTape_eq, le_refl, if_true, Int.toNat_zero,
    List.getElem?_cons_zero] using h

/-- A marked payload overwrite gives the new marked word whenever the marker and its two
new boundary cells have the required values. This also applies when the payload was blank.

**Proof sketch.** Inside the payload, `wordWrite_apply` and the public buffer equation give
the new word. Outside that interval, the framed range contains only the left blank, marker
and right blank supplied by the three hypotheses. -/
private theorem kt_markerWrite_word_of_bounds {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (w : List Bool)
    (hl : d.workTapes r (d.workTapePos r - 1) = none)
    (hm : d.workTapes r (d.workTapePos r) = some true)
    (hr : d.workTapes r (d.workTapePos r + w.length + 1) = none) :
    WordAt { d with workTapes := kt_markerWrite d r r w } r (true :: w) := by
  rw [wordAt_iff]
  intro z hz hz'
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hz'
  change kt_markerWrite d r r w r (d.workTapePos r + z) = FinTM.bufferTape (true :: w) z
  rw [kt_markerWrite, wordWrite_apply]
  simp only [Function.update_self, true_and]
  by_cases hin : 1 ≤ z ∧ z < (w.length : ℤ) + 1
  · rw [if_pos (by omega), show d.workTapePos r + z - (d.workTapePos r + 1) = z - 1 by omega]
    rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos (by omega), if_pos (by omega),
      show z.toNat = (z - 1).toNat + 1 by omega, List.getElem?_cons_succ]
  · rw [if_neg (by omega)]
    rcases (show z = -1 ∨ z = 0 ∨ z = (w.length : ℤ) + 1 by omega) with rfl | rfl | rfl
    · rw [show d.workTapePos r + -1 = d.workTapePos r - 1 by omega, hl,
        FinTM.bufferTape_left]
    · simp only [add_zero, hm, FinTM.bufferTape_eq, le_refl, if_true, Int.toNat_zero,
        List.getElem?_cons_zero]
    · rw [show d.workTapePos r + ((w.length : ℤ) + 1) = d.workTapePos r + w.length + 1 by omega,
        hr, FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_eq_none (by
          simp only [List.length_cons]; omega)]

/-- Overwriting a marked payload with an equally long word preserves both delimiters
and yields the new marked word. The old word supplies precisely the three boundary cells
required by `kt_markerWrite_word_of_bounds`. -/
private theorem kt_markerWrite_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (u w : List Bool)
    (hu : WordAt d r (true :: u)) (hlen : u.length = w.length) :
    WordAt { d with workTapes := kt_markerWrite d r r w } r (true :: w) := by
  apply kt_markerWrite_word_of_bounds
  · have h := (wordAt_iff _ _ _).mp hu (-1) (by omega) (by omega)
    simpa only [sub_eq_add_neg, FinTM.bufferTape_left] using h
  · exact kt_wordAt_marker d r u hu
  · have h := (wordAt_iff _ _ _).mp hu ((w.length : ℤ) + 1) (by omega)
      (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one, hlen]; omega)
    rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_eq_none (by
      simp only [List.length_cons, hlen]; omega)] at h
    simpa only [add_assoc] using h

/-- An equally sized word overwrite preserves both delimiters of an ordinary word.

**Proof sketch.** Inside the overwrite interval the public `wordWrite_apply` equation gives
the new buffer directly. Outside it, the framed interval contains only the left and right
blank; `wordAt_iff` and the equal lengths identify both blanks. -/
private theorem kt_wordWrite_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (u w : List Bool)
    (hu : WordAt d r u) (hlen : u.length = w.length) :
    WordAt { d with workTapes := wordWrite d r w } r w := by
  rw [wordAt_iff] at hu ⊢
  intro z hz hz'
  change wordWrite d r w r (d.workTapePos r + z) = FinTM.bufferTape w z
  rw [wordWrite_apply]
  by_cases hin : 0 ≤ z ∧ z < (w.length : ℤ)
  · rw [if_pos (by omega), show d.workTapePos r + z - d.workTapePos r = z by omega]
  · rw [if_neg (by omega), hu z hz (by rw [hlen]; exact hz')]
    rcases (show z = -1 ∨ z = (w.length : ℤ) by omega) with rfl | rfl
    · rw [FinTM.bufferTape_left, FinTM.bufferTape_left]
    · rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq,
        if_pos (Int.natCast_nonneg _), if_pos (Int.natCast_nonneg _), Int.toNat_natCast,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none le_rfl]

/-- Changing only the control does not change a word overwrite. -/
private theorem kt_wordWrite_state {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (q : Option S) (r : Fin K) (w : List Bool) :
    wordWrite { d with state := q } r w = wordWrite d r w := by
  funext j z
  simp only [wordWrite_apply]

/-! ## Private keyed-table layout facts -/

/-- Keyed tables have two nonempty fields per entry, including empty payloads. -/
private theorem kt_tableWF (es : List (List Bool × List Bool)) :
    TableWF 2 [true] (keyFields es) := by
  rw [tableWF_iff]
  refine ⟨by decide, ?_⟩
  intro e he
  rw [keyFields_def] at he
  obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he
  refine ⟨rfl, ?_⟩
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> exact List.cons_ne_nil _ _

/-- An empty keyed table consists of its one-cell header. -/
private theorem kt_keyTableLength_nil : keyTableLength [] = 1 := by
  simp only [keyTableLength_def, keyFields_def, List.map_nil, tableFields_eq,
    List.flatten_nil, joinFields_singleton, List.length_map, List.length_cons, List.length_nil]

/-- Each entry adds its key and value payloads, two markers and two separators.

**Proof sketch.** Read the keyed layout through `Turing.keyTableLength_def`,
`Turing.keyFields_def` and `Turing.tableFields_eq`. `Turing.joinFields_length` counts field
cells and separators; adjoining the two marked fields gives the stated increment. -/
private theorem kt_keyTableLength_cons (e : List Bool × List Bool)
    (es : List (List Bool × List Bool)) :
    keyTableLength (e :: es) = e.1.length + e.2.length + 4 + keyTableLength es := by
  rw [keyTableLength_def, keyTableLength_def, tableFields_eq, tableFields_eq,
    keyFields_def, keyFields_def, List.map_cons, List.flatten_cons]
  simp only [List.cons_append, List.nil_append]
  rw [joinFields_length _ (List.cons_ne_nil _ _),
    joinFields_length _ (List.cons_ne_nil _ _)]
  simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil]
  omega

/-- Every marked field of a keyed entry is a delimited word when the head is at its offset.

**Proof sketch.** Move only an auxiliary configuration's head to the entry offset, preserving
the table through `Turing.tableAt_iff`. `Turing.TableAt.recordAt_take` gives its two-field
record. Read that record with `Turing.recordAt_iff` and select the field using
`Turing.fieldsTape_field`; `Turing.fieldOffset_add_length_le` bounds the required cells. -/
private theorem kt_table_entry_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool))
    (ht : TableAt d r o [true] (keyFields es)) (j : ℕ) (hj : j < (keyFields es).length)
    (n : ℕ) (hn : n < ((keyFields es)[j]).length)
    (hpos : d.workTapePos r = o + tableOffset [true] (keyFields es) j +
      fieldOffset ((keyFields es)[j]) n) :
    WordAt d r ((keyFields es)[j][n]) := by
  let a : Cfg K Bool S x :=
    { d with workTapePos := Function.update d.workTapePos r (o + tableOffset [true] (keyFields es) j) }
  have hta : TableAt a r o [true] (keyFields es) := by
    rw [tableAt_iff] at ht ⊢
    exact ht
  have hlen : ((keyFields es)[j]).length = 2 :=
    ((tableWF_iff _ _ _).mp (kt_tableWF es)).2 _ (List.getElem_mem hj) |>.1
  have hrec := TableAt.recordAt_take hta (kt_tableWF es) j hj
    (by simp only [a, Function.update_self]) 2 (by decide) le_rfl
  rw [List.take_of_length_le (by omega)] at hrec
  have hspan := fieldOffset_add_length_le ((keyFields es)[j]) n hn
  have hspan' : (fieldOffset ((keyFields es)[j]) n : ℤ) +
      (((keyFields es)[j][n]).length : ℤ) ≤ (joinFields ((keyFields es)[j])).length := by
    exact_mod_cast hspan
  rw [wordAt_iff]
  intro p hp hp'
  rw [hpos, add_assoc]
  have hcell := (recordAt_iff _ _ _).mp hrec
    ((fieldOffset ((keyFields es)[j]) n : ℤ) + p) (by omega) (by omega)
  have hfield := fieldsTape_field ((keyFields es)[j]) n hn p hp hp'
  simpa only [a, Function.update_self, add_assoc] using hcell.trans hfield

/-- The fields of entry `j` are its marked key and marked value. -/
private theorem kt_keyFields_get (es : List (List Bool × List Bool)) (j : ℕ)
    (hj : j < es.length) :
    (keyFields es)[j]'(by rw [keyFields_def, List.length_map]; exact hj) =
      [true :: es[j].1, true :: es[j].2] := by
  simp only [keyFields_def, List.getElem_map]

/-- At an entry's offset, its marked key is a delimited word. -/
private theorem kt_table_key_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool))
    (ht : TableAt d r o [true] (keyFields es)) (j : ℕ) (hj : j < es.length)
    (hpos : d.workTapePos r = o + tableOffset [true] (keyFields es) j) :
    WordAt d r (true :: es[j].1) := by
  have hj' : j < (keyFields es).length := by rw [keyFields_def, List.length_map]; exact hj
  have hget := kt_keyFields_get es j hj
  have h := kt_table_entry_word d r o es ht j hj' 0 (by rw [hget]; exact Nat.zero_lt_succ 1)
    (by rw [fieldOffset_zero, Nat.cast_zero, add_zero]; exact hpos)
  simpa only [hget, List.getElem_cons_zero] using h

/-- After skipping an entry's marked key, its marked value is a delimited word. -/
private theorem kt_table_value_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool))
    (ht : TableAt d r o [true] (keyFields es)) (j : ℕ) (hj : j < es.length)
    (hpos : d.workTapePos r = o + tableOffset [true] (keyFields es) j + es[j].1.length + 2) :
    WordAt d r (true :: es[j].2) := by
  have hj' : j < (keyFields es).length := by rw [keyFields_def, List.length_map]; exact hj
  have hget := kt_keyFields_get es j hj
  have hoff : fieldOffset ((keyFields es)[j]) 1 = es[j].1.length + 2 := by
    rw [hget, fieldOffset_cons_succ, fieldOffset_zero]
    simp only [List.length_cons]
  have h := kt_table_entry_word d r o es ht j hj' 1 (by rw [hget]; exact Nat.lt_succ_self 1)
    (by simpa only [hoff, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hpos)
  simpa only [hget, List.getElem_cons_succ, List.getElem_cons_zero] using h

/-- Every keyed entry has a nonempty list of fields. -/
private theorem kt_entries_ne_nil (es : List (List Bool × List Bool)) :
    ∀ fs ∈ keyFields es, fs ≠ [] := by
  intro fs hfs hnil
  have hlen : fs.length = 2 := ((tableWF_iff _ _ _).mp (kt_tableWF es)).2 fs hfs |>.1
  rw [hnil, List.length_nil] at hlen
  omega

/-- Entry zero starts after the header and its separator; the terminal entry offset is the
second trailing blank, one cell after the layout's length. -/
private theorem kt_tableOffset_endpoints (es : List (List Bool × List Bool)) :
    tableOffset [true] (keyFields es) 0 = 2 ∧
      tableOffset [true] (keyFields es) es.length = keyTableLength es + 1 := by
  constructor
  · rw [tableOffset_eq [true] (keyFields es) (kt_entries_ne_nil es) 0]
    norm_num only [List.length_cons, List.length_nil, List.take_zero, List.map_nil, List.sum_nil]
  · have h := tableOffset_length [true] (keyFields es)
    have hlen : (keyFields es).length = es.length := by rw [keyFields_def, List.length_map]
    rw [hlen, ← keyTableLength_def] at h
    exact h

/-- Advancing past one key and value reaches the next entry's offset. -/
private theorem kt_tableOffset_succ (es : List (List Bool × List Bool)) (j : ℕ)
    (hj : j < es.length) :
    tableOffset [true] (keyFields es) (j + 1) =
      tableOffset [true] (keyFields es) j + es[j].1.length + es[j].2.length + 4 := by
  have hj' : j < (keyFields es).length := by rw [keyFields_def, List.length_map]; exact hj
  rw [tableOffset_eq [true] (keyFields es) (kt_entries_ne_nil es) (j + 1),
    tableOffset_eq [true] (keyFields es) (kt_entries_ne_nil es) j,
    List.take_succ, List.getElem?_eq_getElem hj', Option.toList_some,
    List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [kt_keyFields_get es j hj, joinFields_cons_cons, joinFields_singleton]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

/-- Every entry offset, including a saturated index, is at most the terminal offset. -/
private theorem kt_tableOffset_le_end (es : List (List Bool × List Bool)) (j : ℕ) :
    tableOffset [true] (keyFields es) j ≤ keyTableLength es + 1 := by
  rw [← (kt_tableOffset_endpoints es).2,
    tableOffset_eq [true] (keyFields es) (kt_entries_ne_nil es) j,
    tableOffset_eq [true] (keyFields es) (kt_entries_ne_nil es) es.length]
  have hlen : (keyFields es).length = es.length := by rw [keyFields_def, List.length_map]
  have htake : (keyFields es).take es.length = keyFields es := by
    rw [← hlen, List.take_length]
  rw [htake, List.map_take]
  have hsum := List.sum_take_add_sum_drop
    ((keyFields es).map fun fs => (joinFields fs).length + 1) j
  omega

/-- At the table origin, its header is the delimited one-bit word `[true]`.

**Proof sketch.** The terminal-offset bound implies that the layout contains its header cell.
Read the table through `Turing.tableAt_iff` and its first field through
`Turing.fieldsTape_field`, using `Turing.tableFields_eq` to identify that field. -/
private theorem kt_table_header_word {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool))
    (ht : TableAt d r o [true] (keyFields es)) (hpos : d.workTapePos r = o) :
    WordAt d r [true] := by
  have hlen := kt_tableOffset_le_end es 0
  rw [(kt_tableOffset_endpoints es).1, keyTableLength_def] at hlen
  have hlen' : (1 : ℤ) ≤ ((joinFields (tableFields [true] (keyFields es))).length : ℤ) := by
    exact_mod_cast (show 1 ≤ (joinFields (tableFields [true] (keyFields es))).length by omega)
  have hfs : 0 < (tableFields [true] (keyFields es)).length := by
    rw [tableFields_eq, List.length_cons]
    omega
  have hget : (tableFields [true] (keyFields es))[0]'hfs = [true] := by
    simp only [tableFields_eq, List.getElem_cons_zero]
  rw [wordAt_iff]
  intro p hp hp'
  have hp1 : p ≤ 1 := hp'
  rw [hpos]
  have hcell := (tableAt_iff _ _ _ _ _).mp ht p (by omega) (by omega)
  have hfield := fieldsTape_field (tableFields [true] (keyFields es)) 0 hfs p hp (by rw [hget]; exact hp')
  simp only [fieldOffset_zero, Nat.cast_zero, zero_add, hget] at hfield
  exact hcell.trans hfield

/-! ## Private table controller -/

/-- Read an adapter's retained exit, and return none at every internal control. -/
private def kt_markerExit {S : Type} :
    (Bool ⊕ (Σ p, kt_payloadControl S p)) → Option S
  | .inr ⟨some s, .inr true⟩ => some s
  | _ => none

/-- An adapter control is internal exactly when it is outside the contract's exit set. -/
private theorem kt_markerExit_none_iff {S : Type}
    (q : Bool ⊕ (Σ p, kt_payloadControl S p)) :
    kt_markerExit q = none ↔ some q ∉ (Option.map Sum.inr '' kt_payloadExits S) := by
  cases q with
  | inl b => simp [kt_markerExit, kt_payloadExits, Set.mem_image]
  | inr q =>
    rcases q with ⟨p, c⟩
    cases p with
    | none => simp [kt_markerExit, kt_payloadExits, Set.mem_image]
    | some s =>
      cases c with
      | inl b => cases b <;> simp [kt_markerExit, kt_payloadExits, Set.mem_image]
      | inr b =>
        cases b <;> simp [kt_markerExit, kt_payloadExits, Set.mem_image]
        intro h
        cases h

/-- The finite controller shared by lookup and assignment. The inspection flag records
whether assignment has already found a matching key. -/
private inductive kt_TablePhase where
  | start
  | inspect (found : Bool)
  | compare (found : Bool)
  | skipKey (found matched : Bool)
  | copyValue
  | skipValue (found : Bool)
  | zero
  | appendKeyMarker
  | appendKey
  | skipNewKey
  | appendValueMarker
  | appendValue
  | skipNewValue
  | rewind
  | done
  deriving DecidableEq, Fintype

/-- A constant-zero transducer on the register word. -/
private def kt_zeroStep (_ : Unit) (_ : Bool) : Unit × Bool := ((), false)

/-- Each controller phase runs an existing catalog routine or the shared marker adapter. -/
private def kt_tableControl : kt_TablePhase → Type
  | .start | .skipKey _ _ | .skipValue _ | .skipNewKey | .skipNewValue => SeekPhase
  | .inspect _ => FlagPhase
  | .compare _ => Bool ⊕ (Σ p, kt_payloadControl FlagPhase p)
  | .copyValue | .appendKey | .appendValue => Bool ⊕ (Σ p, kt_payloadControl SweepPhase p)
  | .zero => ScanPhase Unit
  | .rewind => SeekPhase ⊕ SeekPhase
  | .appendKeyMarker | .appendValueMarker | .done => Bool

/-- The phase routines of the five-tape table machine. `assign = false` copies values out;
`assign = true` copies the register into matched fields. The end test compares with the blank
scratch word, so its stop is zero for both a marked field and the blank end. -/
private noncomputable def kt_tableParts (assign : Bool) :
    (p : kt_TablePhase) → MultiTapeTM 5 Bool (kt_tableControl p)
  | .start | .skipKey _ _ | .skipValue _ | .skipNewKey | .skipNewValue => skipTM 5 0
  | .inspect _ => compareTM 5 0 3
  | .compare _ => kt_compareTM 0 1
  | .copyValue => kt_copyTM 0 (if assign then 2 else 0) (if assign then 0 else 2)
  | .zero => scanTM 5 2 kt_zeroStep kt_zeroStep ()
  | .appendKeyMarker | .appendValueMarker => kt_cellTM 0 (some (some true)) 0
  | .appendKey => kt_copyTM 0 1 0
  | .appendValue => kt_copyTM 0 2 0
  | .rewind => tableRewindTM 5 0
  | .done => kt_cellTM 0 none 0

/-- The phase redirects implement first-match lookup or all-match assignment. Assignment
remembers a match until the end, appending only when its flag is still false. -/
private def kt_tableRedirect (assign : Bool) :
    (p : kt_TablePhase) → kt_tableControl p → Option (Σ p, kt_tableControl p)
  | .start, .done => some ⟨.inspect false, .run⟩
  | .start, _ => none
  | .inspect found, .done b =>
      if b then
        if assign then
          if found then some ⟨.rewind, .inl .run⟩ else some ⟨.appendKeyMarker, false⟩
        else
          if found then some ⟨.rewind, .inl .run⟩ else some ⟨.zero, .fwd ()⟩
      else
        if assign || !found then some ⟨.compare found, .inl false⟩
        else some ⟨.skipKey found false, .run⟩
  | .inspect _, _ => none
  | .compare found, q =>
      match kt_markerExit q with
      | some (.done b) => some ⟨.skipKey found b, .run⟩
      | some _ => some ⟨.skipKey found false, .run⟩
      | none => none
  | .skipKey found matched, .done =>
      if matched then some ⟨.copyValue, .inl false⟩ else some ⟨.skipValue found, .run⟩
  | .skipKey _ _, _ => none
  | .copyValue, q =>
      match kt_markerExit q with
      | some _ => some ⟨.skipValue true, .run⟩
      | none => none
  | .skipValue found, .done => some ⟨.inspect found, .run⟩
  | .skipValue _, _ => none
  | .zero, .done _ => some ⟨.rewind, .inl .run⟩
  | .zero, _ => none
  | .appendKeyMarker, true => some ⟨.appendKey, .inl false⟩
  | .appendKeyMarker, false => none
  | .appendKey, q =>
      match kt_markerExit q with
      | some _ => some ⟨.skipNewKey, .run⟩
      | none => none
  | .skipNewKey, .done => some ⟨.appendValueMarker, false⟩
  | .skipNewKey, _ => none
  | .appendValueMarker, true => some ⟨.appendValue, .inl false⟩
  | .appendValueMarker, false => none
  | .appendValue, q =>
      match kt_markerExit q with
      | some _ => some ⟨.skipNewValue, .run⟩
      | none => none
  | .skipNewValue, .done => some ⟨.rewind, .inl .run⟩
  | .skipNewValue, _ => none
  | .rewind, .inr .done => some ⟨.done, false⟩
  | .rewind, _ => none
  | .done, _ => none

/-- The table machine's complete finite control. -/
private abbrev kt_TableState := Σ p : kt_TablePhase, kt_tableControl p

/-- Every phase has a finite local state type. -/
private instance kt_tableControl_fintype (p : kt_TablePhase) : Fintype (kt_tableControl p) := by
  cases p <;> dsimp only [kt_tableControl] <;> infer_instance

/-- The five-tape keyed table controller, assembled with the existing phase host. Its Boolean
parameter selects lookup or assignment; its state type is independent of every word width. -/
private noncomputable def kt_tableTM (assign : Bool) : MultiTapeTM 5 Bool kt_TableState :=
  phaseHostTM (kt_tableParts assign) ⟨.start, .run⟩ (kt_tableRedirect assign)

/-! ## Private phase contracts -/

/-- Local exits at which each catalog row dispatches to its next controller phase. -/
private def kt_tableExits : (p : kt_TablePhase) → Set (Option (kt_tableControl p))
  | .start | .skipKey _ _ | .skipValue _ | .skipNewKey | .skipNewValue =>
      {some SeekPhase.done}
  | .inspect _ => Set.range fun b => some (FlagPhase.done b)
  | .compare _ => Option.map Sum.inr '' kt_payloadExits FlagPhase
  | .copyValue | .appendKey | .appendValue => Option.map Sum.inr '' kt_payloadExits SweepPhase
  | .zero => Set.range fun a => some (ScanPhase.done a)
  | .rewind => {some (.inr .done)}
  | .appendKeyMarker | .appendValueMarker => {some true}
  | .done => ∅

/-- Every local exit dispatches to a different phase, and no internal state dispatches.

**Proof sketch.** The ordinary catalog exits are their terminal constructors. At an adapted
row, `kt_markerExit_none_iff` characterizes the internal controls and `kt_payloadExits` retains
the completed row's control. The redirect equations then identify a different next phase. -/
private theorem kt_table_guards (assign : Bool) (p : kt_TablePhase) :
    none ∉ kt_tableExits p ∧
    (∀ s, some s ∉ kt_tableExits p → kt_tableRedirect assign p s = none) ∧
    (∀ s, some s ∈ kt_tableExits p →
      ∃ q, kt_tableRedirect assign p s = some q ∧ q.1 ≠ p) := by
  constructor
  · cases p <;> simp [kt_tableExits, kt_payloadExits, Set.mem_image]
  constructor
  · intro s hs
    cases p <;> dsimp only [kt_tableControl, kt_tableExits] at s hs
    all_goals first
    | (rw [kt_tableRedirect, (kt_markerExit_none_iff s).mpr hs])
    | (solve | cases s <;> simp_all [kt_tableRedirect])
    | (solve | rcases s with (s | s) <;> cases s <;> simp_all [kt_tableRedirect])
  · intro s hs
    cases p <;> dsimp only [kt_tableControl, kt_tableExits] at s hs
    all_goals first
    | (solve |
       rcases hs with ⟨q, ⟨v, hv⟩, heq⟩
       subst q
       simp only [Option.map_some, Option.some.injEq] at heq
       subst s
       cases v <;> cases assign <;> simp [kt_tableRedirect, kt_markerExit])
    | (solve |
       rcases hs with ⟨⟨⟩, hb⟩
       cases hb
       exact ⟨_, rfl, by simp⟩)
    | (solve |
       rcases hs with ⟨b, hb⟩
       cases hb
       rename_i found
       cases found <;> cases assign <;> cases b <;> simp [kt_tableRedirect])
    | (solve |
       simp only [Set.mem_singleton_iff, Option.some.injEq] at hs
       subst s
       simp only [kt_tableRedirect]
       split_ifs <;> exact ⟨_, rfl, by simp⟩)
    | (solve |
       simp only [Set.mem_singleton_iff, Option.some.injEq] at hs
       subst s
       exact ⟨_, rfl, by simp⟩)
    | (solve | cases hs)


/-- Place a row contract in the shared table controller using the published phase-host
adapter. Every redirect target must belong to a different phase. -/
private def kt_phaseContract {ι : Type} {x : List Bool} (assign : Bool) (p : kt_TablePhase)
    {entry : kt_tableControl p} {X : Set (Option (kt_tableControl p))}
    (C : Contract (kt_tableParts assign p) entry X ι x) (hnone : none ∉ X)
    (hred : ∀ s, some s ∉ X → kt_tableRedirect assign p s = none)
    (hsome : ∀ s, some s ∈ X →
      ∃ q, kt_tableRedirect assign p s = some q ∧ q.1 ≠ p) :
    Contract (kt_tableTM assign) ⟨p, entry⟩
      { q | ∃ s, some s ∈ X ∧ q = kt_tableRedirect assign p s } ι x :=
  Contract.inPhase (kt_tableParts assign) ⟨.start, .run⟩ (kt_tableRedirect assign) p C
    hnone hred hsome

/-- Run any catalog contract in its controller phase, including the one dispatch step.
The local endpoint is read through the public `Contract.inPhase` field equations. -/
private theorem kt_phase_run {ι : Type} {x : List Bool} (assign : Bool) (p : kt_TablePhase)
    {entry : kt_tableControl p}
    (C : Contract (kt_tableParts assign p) entry (kt_tableExits p) ι x)
    (i : ι) (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨p, entry⟩)
    (hp : C.pre i (d.mapState fun _ => entry)) :
    (kt_tableTM assign).runFrom d (C.time i (d.mapState fun _ => entry) + 1) =
      (C.post i (d.mapState fun _ => entry)).bindState (kt_tableRedirect assign p) := by
  have hg := kt_table_guards assign p
  have hp' : (kt_phaseContract assign p C hg.1 hg.2.1 hg.2.2).pre i d := by
    rw [kt_phaseContract, Contract.inPhase_pre]
    exact hp
  have h := (kt_phaseContract assign p C hg.1 hg.2.1 hg.2.2).run i d hd hp'
  simpa only [kt_phaseContract, Contract.inPhase_time, Contract.inPhase_post] using h

/-- The published table-rewind row, packaged as a framed contract for the final phase.

**Proof sketch.** `Turing.tableRewindTM_run_ofCfg` supplies the exact endpoint, first-exit cut
and head bounds. `Turing.framedContract` packages these clauses without changing them. -/
private def kt_rewindContract {x : List Bool} :
    Contract (tableRewindTM 5 (0 : Fin 5)) (.inl .run) {some (.inr .done)}
      (List (List Bool)) x :=
  framedContract (tableRewindTM 5 (0 : Fin 5)) (.inl .run) (.inr .done) x
    (fun ws d => ws ≠ [] ∧ (∀ u ∈ ws, u ≠ []) ∧
      ∀ p : ℤ, -2 ≤ p → p < (fieldOffset ws ws.length : ℤ) →
        d.workTapes 0 (d.workTapePos 0 - fieldOffset ws ws.length + p) = fieldsTape ws p)
    (fun ws _ => fieldOffset ws ws.length + 7)
    (fun ws d =>
      { d with
        state := some (.inr .done)
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 - fieldOffset ws ws.length) })
    (fun j => j = (0 : Fin 5))
    (fun ws d j => d.workTapePos j - fieldOffset ws ws.length - 2)
    (fun _ d j => d.workTapePos j)
    (fun _ _ => rfl)
    (fun ws d hd hp => tableRewindTM_run_ofCfg (0 : Fin 5) ws hp.1 hp.2.1 d hd hp.2.2)

/-- Entry control of each local catalog contract. -/
private def kt_phaseEntry : (p : kt_TablePhase) → kt_tableControl p
  | .start | .skipKey _ _ | .skipValue _ | .skipNewKey | .skipNewValue => .run
  | .inspect _ => .run
  | .compare _ | .copyValue | .appendKey | .appendValue => .inl false
  | .zero => .fwd ()
  | .rewind => .inl .run
  | .appendKeyMarker | .appendValueMarker | .done => false

/-- The constant-zero transducer preserves length and replaces every bit by false. -/
private theorem kt_zero_mealy (w : List Bool) :
    mealyRun kt_zeroStep () w = ((), List.replicate w.length false) := by
  induction w with
  | nil => simp only [mealyRun_nil, List.length_nil, List.replicate_zero]
  | cons b w ih =>
    simp only [mealyRun_cons, kt_zeroStep, ih, List.length_cons, List.replicate_succ]

/-- Both passes of the zero scan leave exactly the same-length zero word. -/
private theorem kt_zero_scanResult (w : List Bool) :
    scanResult kt_zeroStep kt_zeroStep () w = ((), List.replicate w.length false) := by
  simp only [scanResult_eq, kt_zero_mealy, List.length_replicate,
    List.reverse_replicate]

/-- The catalog zero scan writes only the register's original interval and returns all heads. -/
private theorem kt_zero_contract_post {K : ℕ} {x : List Bool} (r : Fin K) (w : List Bool)
    (d : Cfg K Bool (ScanPhase Unit) x) :
    (scanTM_contract r kt_zeroStep kt_zeroStep () x).post w d =
      { d with state := some (.done ()), workTapes := wordWrite d r (List.replicate w.length false) } := by
  rw [scanTM_contract_post, kt_zero_scanResult]
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext j q
  change (if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then
      FinTM.bufferTape (List.replicate w.length false) (q - d.workTapePos j)
      else d.workTapes j q) = wordWrite d r (List.replicate w.length false) j q
  rw [wordWrite_apply, List.length_replicate]

/-! ## Private traversal frames -/

/-- A controller configuration with a chosen control and table head, all other physical
fields supplied by one fixed configuration. -/
private def kt_at {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (q : kt_TableState) (h : ℤ) : Cfg 5 Bool kt_TableState x :=
  { d with state := some q, workTapePos := Function.update d.workTapePos 0 h }

/-- Reframing twice keeps only the last chosen controller state and table head. -/
private theorem kt_at_at {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (q q' : kt_TableState) (h h' : ℤ) :
    kt_at (kt_at d q h) q' h' = kt_at d q' h' := by
  simp only [kt_at, Function.update_idem]

/-- Moving only the table head preserves a word overwrite on any other tape. -/
private theorem kt_wordWrite_at_other {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (q : kt_TableState) (h : ℤ) (r : Fin 5) (hne : r ≠ 0) (w : List Bool) :
    wordWrite (kt_at d q h) r w = wordWrite d r w := by
  funext j z
  rw [wordWrite_apply, wordWrite_apply]
  by_cases hj : j = r
  · subst j
    simp only [kt_at, Function.update_of_ne hne]
  · simp only [hj, false_and, if_false, kt_at]

/-- The five uses of a field skip differ only in their controller continuation. -/
private inductive kt_SkipKind where
  | start
  | key (found matched : Bool)
  | value (found : Bool)
  | newKey
  | newValue

/-- The controller phase of a field skip. -/
private def kt_skipPhase : kt_SkipKind → kt_TablePhase
  | .start => .start
  | .key f m => .skipKey f m
  | .value f => .skipValue f
  | .newKey => .skipNewKey
  | .newValue => .skipNewValue

/-- The continuation of each use of the same field skip. -/
private def kt_afterSkip : kt_SkipKind → kt_TableState
  | .start => ⟨.inspect false, .run⟩
  | .key f m => if m then ⟨.copyValue, .inl false⟩ else ⟨.skipValue f, .run⟩
  | .value f => ⟨.inspect f, .run⟩
  | .newKey => ⟨.appendValueMarker, false⟩
  | .newValue => ⟨.rewind, .inl .run⟩

/-- Every field skip takes its word length plus two steps, dispatch included, and preserves
all cells while advancing to the next field.

**Proof sketch.** Place `Turing.skipTM_contract` with `kt_phase_run`. Its precondition reads
the nonnegative offsets of the supplied word, and its endpoint is `Turing.seekPost`.
The five continuations differ only at the dispatch; read the configuration fields to obtain
one common framed endpoint. -/
private theorem kt_skip_run {x : List Bool} (assign : Bool) (kind : kt_SkipKind)
    (w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨kt_skipPhase kind, kt_phaseEntry (kt_skipPhase kind)⟩)
    (hw : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape w p) :
    (kt_tableTM assign).runFrom d (w.length + 2) =
      kt_at d (kt_afterSkip kind) (d.workTapePos 0 + w.length + 1) := by
  let p := kt_skipPhase kind
  cases kind
  all_goals
    have hp : (skipTM_contract (0 : Fin 5) x).pre w (d.mapState fun _ => SeekPhase.run) := by
      rw [skipTM_contract_pre]
      simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hw
    have h := kt_phase_run assign p (skipTM_contract (0 : Fin 5) x) w d hd hp
    simp only [skipTM_contract_time, skipTM_contract_post] at h
    refine h.trans ?_
    apply Cfg.ext
    · simp only [Cfg.bindState_state, seekPost_state, Option.bind_some, kt_tableRedirect,
        kt_at, kt_afterSkip, p, kt_skipPhase] <;> split_ifs <;> rfl
    · simp only [Cfg.bindState_inputPos, seekPost_inputPos, Cfg.mapState_inputPos, kt_at]
    · funext j q
      simp only [Cfg.bindState_workTapes, seekPost_workTapes, Cfg.mapState_workTapes, kt_at]
    · funext j
      simp only [Cfg.bindState_workTapePos, seekPost_workTapePos,
        Cfg.mapState_workTapePos, kt_at, Function.update_apply]
    · simp only [Cfg.bindState_output, seekPost_output, Cfg.mapState_output, kt_at]

/-- Inspecting a field against the blank scratch word takes three steps, dispatch included,
and changes only the controller state.

**Proof sketch.** The scratch comparison has stop zero by `Turing.compareStop_le`.
Place its published contract with `kt_phase_run`, read its exact endpoint, and retain only
the dispatch control; every physical field is unchanged. -/
private theorem kt_inspect_run {x : List Bool} (assign found : Bool) (u : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.inspect found, .run⟩)
    (hu : WordAt d 0 u) (hs : WordAt d 3 []) :
    (kt_tableTM assign).runFrom d 3 =
      { d with state := kt_tableRedirect assign (.inspect found) (.done (decide (u = []))) } := by
  have hz : compareStop u ([] : List Bool) = 0 := by
    have h := compareStop_le u ([] : List Bool)
    simp only [List.length_nil, Nat.min_zero] at h
    omega
  have hp : (compareTM_contract (0 : Fin 5) 3 (of_decide_eq_true rfl) x).pre (u, [])
      (d.mapState fun _ => FlagPhase.run) := by
    rw [compareTM_contract_pre]
    constructor
    · simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using (wordAt_iff _ _ _).mp hu
    · simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using (wordAt_iff _ _ _).mp hs
  have h := kt_phase_run assign (.inspect found)
    (compareTM_contract (0 : Fin 5) 3 (of_decide_eq_true rfl) x) (u, []) d hd hp
  rw [compareTM_contract_time, hz, compareTM_contract_post] at h
  refine h.trans ?_
  apply Cfg.ext
  · simp only [Cfg.bindState_state, Option.bind_some]
  · simp only [Cfg.bindState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.bindState_workTapes, Cfg.mapState_workTapes]
  · funext j
    simp only [Cfg.bindState_workTapePos, Cfg.mapState_workTapePos]
  · simp only [Cfg.bindState_output, Cfg.mapState_output]

/-- The comparison phase restores its complete physical frame and dispatches the verdict
into the following key skip.

**Proof sketch.** Apply the precondition and exact-time reader of the shared adapted
comparison to the locally relabeled configuration, then place the row with `kt_phase_run`.
Its framed postcondition retains the comparison's Boolean verdict through marker restoration. -/
private theorem kt_compare_run {x : List Bool} (assign found : Bool) (u k : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.compare found, .inl false⟩)
    (hu : WordAt d 0 (true :: u)) (hk : WordAt d 1 k)
    (hm : d.workTapes 0 (d.workTapePos 0) = some true) :
    (kt_tableTM assign).runFrom d (2 * compareStop u k + 9) =
      { d with state := some ⟨.skipKey found (decide (u = k)), .run⟩ } := by
  let c := d.mapState fun _ => (Sum.inl false : Bool ⊕ (Σ p, kt_payloadControl FlagPhase p))
  have hc : c.state = some (.inl false) := by
    simp only [c, Cfg.mapState_state, hd, Option.map_some]
  have hp := kt_compareContract_pre_time (0 : Fin 5) 1 (of_decide_eq_true rfl) u k c hc
    (kt_wordAt_mapState d _ 0 _ hu) (kt_wordAt_mapState d _ 1 k hk)
  have hpost := kt_compareContract_post (0 : Fin 5) 1 (of_decide_eq_true rfl) u k c hc
    (by simpa only [c, Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hm)
  have h := kt_phase_run assign (.compare found)
    (kt_compareContract (0 : Fin 5) 1 (of_decide_eq_true rfl)) (u, k) d hd hp.1
  change (kt_tableTM assign).runFrom d ((kt_compareContract (0 : Fin 5) 1
      (of_decide_eq_true rfl)).time (u, k) c + 1) = _ at h
  rw [hp.2, hpost] at h
  refine h.trans ?_
  apply Cfg.ext
  · simp only [Cfg.bindState_state, Option.bind_some, kt_tableRedirect, kt_markerExit]
  · simp only [Cfg.bindState_inputPos, c, Cfg.mapState_inputPos]
  · funext j q
    simp only [Cfg.bindState_workTapes, c, Cfg.mapState_workTapes]
  · funext j
    simp only [Cfg.bindState_workTapePos, c, Cfg.mapState_workTapePos]
  · simp only [Cfg.bindState_output, c, Cfg.mapState_output]

/-- The three uses of the shared adapted copy. -/
private inductive kt_CopyKind where
  | value
  | newKey
  | newValue

/-- Controller phase of an adapted copy. -/
private def kt_copyPhase : kt_CopyKind → kt_TablePhase
  | .value => .copyValue
  | .newKey => .appendKey
  | .newValue => .appendValue

/-- Source tape of each adapted copy. -/
private def kt_copySrc (assign : Bool) : kt_CopyKind → Fin 5
  | .value => if assign then 2 else 0
  | .newKey => 1
  | .newValue => 2

/-- Destination tape of each adapted copy. -/
private def kt_copyDst (assign : Bool) : kt_CopyKind → Fin 5
  | .value => if assign then 0 else 2
  | .newKey | .newValue => 0

/-- Every adapted copy returns to a skip of the field just read or written. -/
private def kt_afterCopy : kt_CopyKind → kt_TableState
  | .value => ⟨.skipValue true, .run⟩
  | .newKey => ⟨.skipNewKey, .run⟩
  | .newValue => ⟨.skipNewValue, .run⟩

/-- Every use of copying has distinct source and destination tapes. -/
private theorem kt_copyKind_ne (assign : Bool) (kind : kt_CopyKind) :
    kt_copySrc assign kind ≠ kt_copyDst assign kind := by
  cases kind <;> cases assign <;> decide

/-- Read the complete tape vector of a state relabeling through its pointwise public reader. -/
private theorem kt_mapState_workTapes {K : ℕ} {S U : Type} {x : List Bool}
    (d : Cfg K Bool S x) (f : S → U) : (d.mapState f).workTapes = d.workTapes := by
  funext j q
  rw [Cfg.mapState_workTapes]

/-- Each copy phase takes twice the payload length plus nine steps, including dispatch,
returns every head, and overwrites exactly the adapted destination interval.

**Proof sketch.** Relabel the local start without changing its opened source word.
`kt_copyContract_pre_time` and `kt_copyContract_post` supply the single shared adapter's
specification. `kt_phase_run` places it in each of its three controller phases; reading the
state binding and the overwrite equation gives the common endpoint. -/
private theorem kt_copy_run {x : List Bool} (assign : Bool) (kind : kt_CopyKind)
    (w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨kt_copyPhase kind, kt_phaseEntry (kt_copyPhase kind)⟩)
    (hw : WordAt (kt_openMarker d 0) (kt_copySrc assign kind) w)
    (hm : d.workTapes 0 (d.workTapePos 0) = some true) :
    (kt_tableTM assign).runFrom d (2 * w.length + 9) =
      { d with
        state := some (kt_afterCopy kind)
        workTapes := kt_markerWrite d 0 (kt_copyDst assign kind) w } := by
  let p := kt_copyPhase kind
  let src := kt_copySrc assign kind
  let dst := kt_copyDst assign kind
  let hne := kt_copyKind_ne assign kind
  let c := d.mapState fun _ => (Sum.inl false : Bool ⊕ (Σ p, kt_payloadControl SweepPhase p))
  have hc : c.state = some (.inl false) := by
    simp only [c, Cfg.mapState_state, hd, Option.map_some]
  have hwc : WordAt (kt_openMarker c 0) src w := by
    simpa only [wordAt_iff, c, kt_openMarker, kt_mapState_workTapes,
      Cfg.mapState_workTapePos, Function.update_apply, src] using hw
  have hp := kt_copyContract_pre_time (0 : Fin 5) src dst hne w c hc hwc
  have hpost := kt_copyContract_post (0 : Fin 5) src dst hne w c hc
    (by simpa only [c, Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using hm)
  cases kind
  all_goals
    have h := kt_phase_run assign p (kt_copyContract (0 : Fin 5) src dst hne) w d hd hp.1
    change (kt_tableTM assign).runFrom d
      ((kt_copyContract (0 : Fin 5) src dst hne).time w c + 1) = _ at h
    rw [hp.2, hpost] at h
    refine h.trans ?_
    apply Cfg.ext
    · simp only [Cfg.bindState_state, Option.bind_some, kt_tableRedirect, kt_markerExit,
        p, kt_copyPhase, kt_afterCopy]
    · simp only [Cfg.bindState_inputPos, c, Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.bindState_workTapes, kt_markerWrite, wordWrite_apply, c,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_apply, dst]
    · funext j
      simp only [Cfg.bindState_workTapePos, c, Cfg.mapState_workTapePos]
    · simp only [Cfg.bindState_output, c, Cfg.mapState_output]

/-- The final rewind from the second blank after a keyed table returns to its origin,
leaving every cell fixed, in the layout length plus nine steps.

**Proof sketch.** The table fields are nonempty by `kt_tableWF`, and their end offset is
the layout length plus one. `Turing.tableAt_iff` supplies the rewind's framed precondition.
Place `kt_rewindContract` through `kt_phase_run` and read its endpoint and time via
`Turing.framedContract`'s equations. -/
private theorem kt_rewind_run {x : List Bool} (assign : Bool)
    (o : ℤ) (es : List (List Bool × List Bool)) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨.rewind, .inl .run⟩)
    (hpos : d.workTapePos 0 = o + (keyTableLength es : ℤ) + 1)
    (ht : TableAt d 0 o [true] (keyFields es)) :
    (kt_tableTM assign).runFrom d (keyTableLength es + 9) = kt_at d ⟨.done, false⟩ o := by
  let ws := tableFields [true] (keyFields es)
  have hws : ws ≠ [] := by
    change tableFields [true] (keyFields es) ≠ []
    rw [tableFields_eq]
    exact List.cons_ne_nil _ _
  have hoff : fieldOffset ws ws.length = keyTableLength es + 1 := by
    rw [fieldOffset_length ws hws, keyTableLength_def]
  have hp : (kt_rewindContract (x := x)).pre ws
      (d.mapState fun _ => (Sum.inl SeekPhase.run : SeekPhase ⊕ SeekPhase)) := by
    rw [kt_rewindContract, framedContract_pre]
    refine ⟨hws, TableWF.field_ne_nil (kt_tableWF es), ?_⟩
    intro z hz hz'
    simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hoff, Nat.cast_add,
      Nat.cast_one, hpos]
    rw [show o + (keyTableLength es : ℤ) + 1 - ((keyTableLength es : ℤ) + 1) + z = o + z by omega]
    exact (tableAt_iff _ _ _ _ _).mp ht z hz (by
      rw [keyTableLength_def] at hoff
      rw [hoff] at hz'
      exact le_of_lt hz')
  have h := kt_phase_run assign .rewind kt_rewindContract ws d hd hp
  simp only [kt_rewindContract, framedContract_time, framedContract_post, hoff] at h
  refine h.trans ?_
  apply Cfg.ext
  · simp only [Cfg.bindState_state, Option.bind_some, kt_tableRedirect, kt_at]
  · simp only [Cfg.bindState_inputPos, Cfg.mapState_inputPos, kt_at]
  · funext j q
    simp only [Cfg.bindState_workTapes, Cfg.mapState_workTapes, kt_at]
  · funext j
    simp only [Cfg.bindState_workTapePos, Cfg.mapState_workTapePos, Function.update_apply,
      kt_at, Nat.cast_add, Nat.cast_one, hpos]
    split_ifs <;> omega
  · simp only [Cfg.bindState_output, Cfg.mapState_output, kt_at]

/-- The zero-register phase keeps its word width and dispatches to the final rewind.

**Proof sketch.** Place the catalog scan with `kt_phase_run` and use
`kt_zero_contract_post` to identify the same-width zero overwrite. Read the state binding
and state relabeling through their field equations to obtain the complete framed endpoint. -/
private theorem kt_zero_run {x : List Bool} (assign : Bool) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.zero, .fwd ()⟩)
    (hw : WordAt d 2 w) :
    (kt_tableTM assign).runFrom d (2 * w.length + 3) =
      { d with
        state := some ⟨.rewind, .inl .run⟩
        workTapes := wordWrite d 2 (List.replicate w.length false) } := by
  have hp : (scanTM_contract (2 : Fin 5) kt_zeroStep kt_zeroStep () x).pre w
      (d.mapState fun _ => ScanPhase.fwd ()) := by
    rw [scanTM_contract_pre]
    simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos] using (wordAt_iff _ _ _).mp hw
  have h := kt_phase_run assign .zero
    (scanTM_contract (2 : Fin 5) kt_zeroStep kt_zeroStep () x) w d hd hp
  rw [scanTM_contract_time, kt_zero_contract_post] at h
  refine h.trans ?_
  apply Cfg.ext
  · simp only [Cfg.bindState_state, Option.bind_some, kt_tableRedirect]
  · simp only [Cfg.bindState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.bindState_workTapes]
    change wordWrite (d.mapState fun _ => ScanPhase.fwd ()) 2 (List.replicate w.length false) j q =
      wordWrite d 2 (List.replicate w.length false) j q
    by_cases hwrite : j = 2 ∧ d.workTapePos j ≤ q ∧
        q < d.workTapePos j + ((List.replicate w.length false).length : ℤ) <;>
      simp only [wordWrite_apply, Cfg.mapState_workTapePos, Cfg.mapState_workTapes,
        hwrite, if_false]
  · funext j
    simp only [Cfg.bindState_workTapePos, Cfg.mapState_workTapePos]
  · simp only [Cfg.bindState_output, Cfg.mapState_output]

/-- Whether this entry is copied: assignment tests every entry; lookup tests until its
first match and then only skips the remaining fields. -/
private def kt_match (assign found : Bool) (u k : List Bool) : Bool :=
  (assign || !found) && decide (u = k)

/-- Inspect and, when needed, compare one entry's key; the whole physical frame is restored.

**Proof sketch.** `kt_inspect_run` tests the nonempty marked field in three steps. If the
found flag already finishes lookup, it dispatches directly to a mismatch skip. Otherwise
`kt_compare_run` gives the key verdict. `Turing.compareStop_le` bounds the comparison by the
stored key's length, including when the query is much longer. -/
private theorem kt_searchKey_run {x : List Bool} (assign found : Bool) (u k : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.inspect found, .run⟩)
    (hu : WordAt d 0 (true :: u)) (hk : WordAt d 1 k) (hs : WordAt d 3 []) :
    ∃ t ≤ 2 * u.length + 12, (kt_tableTM assign).runFrom d t =
      { d with state := some ⟨.skipKey found (kt_match assign found u k), .run⟩ } := by
  have hi := kt_inspect_run assign found (true :: u) d hd hu hs
  cases hsearch : (assign || !found) with
  | false =>
    refine ⟨3, by omega, ?_⟩
    simp only [kt_match]
    rw [hsearch]
    simpa [kt_tableRedirect, hsearch] using hi
  | true =>
    simp [kt_tableRedirect, hsearch] at hi
    let c : Cfg 5 Bool kt_TableState x := { d with state := some ⟨.compare found, .inl false⟩ }
    have hc := kt_compare_run assign found u k c rfl
      (by simpa only [wordAt_iff, c] using hu)
      (by simpa only [wordAt_iff, c] using hk)
      (by simpa only [c] using kt_wordAt_marker d 0 u hu)
    refine ⟨3 + (2 * compareStop u k + 9), ?_, ?_⟩
    · have hstop := (compareStop_le u k).trans (Nat.min_le_left _ _)
      omega
    · rw [MultiTapeTM.runFrom_add, hi]
      simp only [kt_match]
      rw [hsearch]
      simpa only [c, Bool.true_and] using hc

/-- The overwrite at a matched value: into the marked payload for assignment, or into
the ordinary register word for lookup. -/
private def kt_valueWrite {x : List Bool} (assign : Bool) (d : Cfg 5 Bool kt_TableState x)
    (v w : List Bool) : Fin 5 → ℤ → Option Bool :=
  kt_markerWrite d 0 (kt_copyDst assign .value) (if assign then w else v)

/-- The framed result of processing a value and advancing to the next entry. -/
private def kt_valuePost {x : List Bool} (assign found matched : Bool)
    (d : Cfg 5 Bool kt_TableState x) (v w : List Bool) : Cfg 5 Bool kt_TableState x :=
  kt_at { d with workTapes := if matched then kt_valueWrite assign d v w else d.workTapes }
    ⟨.inspect (found || matched), .run⟩ (d.workTapePos 0 + (true :: v).length + 1)

/-- Process one value, copying it only when matched, and skip to the next entry.

**Proof sketch.** A mismatch is `kt_skip_run`. On a match, choose the register word for
assignment and the stored payload for lookup, and apply the one `kt_copy_run` theorem.
`kt_markerWrite_word` preserves an assigned field's delimiters; copying outward preserves
the table tape. The same field skip then returns to inspection with the found flag true. -/
private theorem kt_value_run {x : List Bool} (assign found matched : Bool)
    (v w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = if matched then some ⟨.copyValue, .inl false⟩
      else some ⟨.skipValue found, .run⟩)
    (hv : WordAt d 0 (true :: v)) (hw : WordAt d 2 w) (hlen : v.length = w.length) :
    ∃ t ≤ 3 * v.length + 12, (kt_tableTM assign).runFrom d t =
      kt_valuePost assign found matched d v w := by
  cases matched with
  | false =>
    have h := kt_skip_run assign (.value found) (true :: v) d hd
      (fun z hz hz' => (wordAt_iff _ _ _).mp hv z (by omega) hz')
    refine ⟨(true :: v).length + 2, by simp only [List.length_cons]; omega, ?_⟩
    rw [kt_valuePost, Bool.or_false]
    simpa only [Bool.false_eq_true, if_false, kt_afterSkip] using h
  | true =>
    let a := if assign then w else v
    have ha : a.length = v.length := by cases assign <;> simp only [a, Bool.false_eq_true,
      if_false, if_true, hlen]
    let e : Cfg 5 Bool kt_TableState x :=
      { d with
        state := some ⟨.skipValue true, .run⟩
        workTapes := kt_valueWrite assign d v w }
    have hopen : WordAt (kt_openMarker d 0) (kt_copySrc assign .value) a := by
      cases assign with
      | false => exact kt_openMarker_word d 0 v hv
      | true => exact kt_openMarker_word_other d 0 2 (of_decide_eq_true rfl) w hw
    have hc : (kt_tableTM assign).runFrom d (2 * a.length + 9) = e := by
      simpa only [e, kt_valueWrite, a, kt_afterCopy] using
        kt_copy_run assign .value a d hd hopen (kt_wordAt_marker d 0 v hv)
    have hew : WordAt e 0 (true :: a) := by
      cases assign with
      | false =>
        have hwrite : kt_valueWrite false d v w = wordWrite d 2 v :=
          kt_markerWrite_other d 0 2 (of_decide_eq_true rfl) v
        simpa only [wordAt_iff, e, a, Bool.false_eq_true, if_false, hwrite, wordWrite_apply,
          show (0 : Fin 5) ≠ 2 by decide, false_and, if_false] using hv
      | true =>
        simpa only [wordAt_iff, e, a, kt_valueWrite, kt_copyDst, if_true] using
          kt_markerWrite_word d 0 v w hv hlen
    have hs := kt_skip_run assign (.value true) (true :: a) e rfl
      (fun z hz hz' => (wordAt_iff _ _ _).mp hew z (by omega) hz')
    have hmarklen : (true :: a).length = (true :: v).length := by simp only [List.length_cons, ha]
    rw [hmarklen] at hs
    refine ⟨2 * a.length + 9 + ((true :: v).length + 2), ?_, ?_⟩
    · simp only [List.length_cons, ha]
      omega
    · rw [MultiTapeTM.runFrom_add, hc, hs]
      rw [kt_valuePost, Bool.or_true]
      simp only [if_true, kt_afterSkip, kt_at, e]

/-- The result of one entry scan, expressed through the common value-step frame. -/
private def kt_entryPost {x : List Bool} (assign found : Bool) (u v k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) : Cfg 5 Bool kt_TableState x :=
  let matched := kt_match assign found u k
  let e := kt_at d (kt_afterSkip (.key found matched))
    (d.workTapePos 0 + (true :: u).length + 1)
  kt_valuePost assign found matched e v w

/-- One complete entry scan costs at most eight times that entry's layout contribution.

**Proof sketch.** `kt_searchKey_run` inspects and compares the key, `kt_skip_run` crosses its
marked field, and `kt_value_run` copies or skips the value. Concatenate their exact runs with
`Turing.MultiTapeTM.runFrom_add`. Their bounds sum to at most
`3|u| + 3|v| + 27`, below `8(|u| + |v| + 4)`. -/
private theorem kt_entry_run {x : List Bool} (assign found : Bool) (u v k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.inspect found, .run⟩)
    (hu : WordAt d 0 (true :: u))
    (hv : WordAt (kt_at d ⟨.copyValue, .inl false⟩
      (d.workTapePos 0 + (true :: u).length + 1)) 0 (true :: v))
    (hk : WordAt d 1 k) (hw : WordAt d 2 w) (hs : WordAt d 3 [])
    (hlen : v.length = w.length) :
    ∃ t ≤ 8 * (u.length + v.length + 4), (kt_tableTM assign).runFrom d t =
      kt_entryPost assign found u v k w d := by
  obtain ⟨t, ht, hr⟩ := kt_searchKey_run assign found u k d hd hu hk hs
  let matched := kt_match assign found u k
  let c : Cfg 5 Bool kt_TableState x :=
    { d with state := some ⟨.skipKey found matched, .run⟩ }
  let e := kt_at d (kt_afterSkip (.key found matched))
    (d.workTapePos 0 + (true :: u).length + 1)
  have hkey : WordAt c 0 (true :: u) := by simpa only [wordAt_iff, c] using hu
  have hskip : (kt_tableTM assign).runFrom c ((true :: u).length + 2) = e := by
    simpa only [e, c, kt_at] using kt_skip_run assign (.key found matched) (true :: u) c rfl
      (fun z hz hz' => (wordAt_iff _ _ _).mp hkey z (by omega) hz')
  have he : e.state = if matched then some ⟨.copyValue, .inl false⟩
      else some ⟨.skipValue found, .run⟩ := by
    simp only [e, kt_at, kt_afterSkip]
    split_ifs <;> rfl
  have hvalue : WordAt e 0 (true :: v) := by simpa only [wordAt_iff, e, kt_at] using hv
  have hreg : WordAt e 2 w := by
    simpa only [wordAt_iff, e, kt_at,
      Function.update_of_ne (show (2 : Fin 5) ≠ 0 by decide)] using hw
  obtain ⟨tv, htv, hval⟩ := kt_value_run assign found matched v w e he hvalue hreg hlen
  refine ⟨t + (((true :: u).length + 2) + tv), ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · rw [MultiTapeTM.runFrom_add, hr, MultiTapeTM.runFrom_add, hskip, hval]
    rfl

/-- Lookup's value copy is an ordinary register overwrite. -/
private theorem kt_valueWrite_lookup {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (v w : List Bool) : kt_valueWrite false d v w = wordWrite d 2 v :=
  kt_markerWrite_other d 0 2 (of_decide_eq_true rfl) v

/-- An adapted overwrite depends on the table-head frame and physical fields, not its control. -/
private theorem kt_markerWrite_at_control {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (q q' : kt_TableState) (h : ℤ) (r dst : Fin 5) (w : List Bool) :
    kt_markerWrite (kt_at d q h) r dst w = kt_markerWrite (kt_at d q' h) r dst w := by
  let b : Cfg 5 Bool kt_TableState x :=
    { d with
      workTapePos :=
        Function.update (Function.update d.workTapePos 0 h) r
          ((Function.update d.workTapePos 0 h) r + 1) }
  change wordWrite { b with state := some q } dst w = wordWrite { b with state := some q' } dst w
  rw [kt_wordWrite_state, kt_wordWrite_state]

/-- The shared entry endpoint has a canonical value-head frame independent of the control
that dispatched to copying, and advances by the entry's layout contribution.

**Proof sketch.** Read the common value-step endpoint and use
`kt_markerWrite_at_control` to choose the same value frame in either mode. The remaining
configuration fields agree directly; the nested updates of the table head collapse, and the
two marked-field lengths give the stated displacement. -/
private theorem kt_entryPost_frame {x : List Bool} (assign found : Bool) (u v k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) :
    kt_entryPost assign found u v k w d =
      kt_at { d with workTapes := if kt_match assign found u k then
          kt_valueWrite assign (kt_at d ⟨.copyValue, .inl false⟩
            (d.workTapePos 0 + (true :: u).length + 1)) v w else d.workTapes }
        ⟨.inspect (found || kt_match assign found u k), .run⟩
        (d.workTapePos 0 + u.length + v.length + 4) := by
  dsimp only [kt_entryPost, kt_valuePost]
  simp only [kt_valueWrite]
  rw [kt_markerWrite_at_control d
    (kt_afterSkip (.key found (kt_match assign found u k))) ⟨.copyValue, .inl false⟩
    (d.workTapePos 0 + (true :: u).length + 1) 0 (kt_copyDst assign .value) (if assign then w else v)]
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  by_cases hj : j = 0
  · subst j
    simp only [kt_at, Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega
  · simp only [kt_at, Function.update_of_ne hj]

/-- A lookup entry preserves the table and either keeps the register or copies the first
matching value into it; the table head advances by precisely the entry's layout contribution. -/
private theorem kt_entryPost_lookup {x : List Bool} (found : Bool) (u v k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) :
    kt_entryPost false found u v k w d =
      kt_at { d with workTapes := if kt_match false found u k then wordWrite d 2 v else d.workTapes }
        ⟨.inspect (found || kt_match false found u k), .run⟩
        (d.workTapePos 0 + u.length + v.length + 4) := by
  rw [kt_entryPost_frame, kt_valueWrite_lookup,
    kt_wordWrite_at_other d _ _ 2 (of_decide_eq_true rfl) v]

/-- Lookup reads the first matching entry and otherwise continues with the tail. -/
private theorem kt_keyLookup_cons (e : List Bool × List Bool)
    (es : List (List Bool × List Bool)) (k : List Bool) :
    keyLookup (e :: es) k = if e.1 = k then some e.2 else keyLookup es k := by
  by_cases h : e.1 = k <;>
    simp only [keyLookup_def, List.find?_cons, h, decide_true, decide_false,
      if_true, if_false, Option.map_some]

/-- A register overwrite combined with a new table head and controller control. -/
private def kt_registerFrame {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (write : Bool) (v : List Bool) (q : kt_TableState) (h : ℤ) : Cfg 5 Bool kt_TableState x :=
  kt_at { d with workTapes := if write then wordWrite d 2 v else d.workTapes } q h

/-- The lookup register frame preserves the table, query and blank scratch word, and its
new register is delimited with the original width.

**Proof sketch.** `wordWrite_apply` keeps every tape other than tape 2. The chosen table head
changes no other head. Read the preserved predicates through `keyTableAt_iff`, `tableAt_iff`
and `wordAt_iff`; for the updated register use `kt_wordWrite_word`. -/
private theorem kt_registerFrame_invariants {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (write : Bool) (v w k : List Bool) (q : kt_TableState) (h o : ℤ)
    (es : List (List Bool × List Bool)) (ht : KeyTableAt d 0 o es)
    (hk : WordAt d 1 k) (hw : WordAt d 2 w) (hs : WordAt d 3 []) (hlen : v.length = w.length) :
    KeyTableAt (kt_registerFrame d write v q h) 0 o es ∧
    WordAt (kt_registerFrame d write v q h) 1 k ∧
    WordAt (kt_registerFrame d write v q h) 2 (if write then v else w) ∧
    WordAt (kt_registerFrame d write v q h) 3 [] ∧
    (if write then v else w).length = w.length := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [keyTableAt_iff, tableAt_iff, kt_registerFrame, kt_at, ite_apply, wordWrite_apply,
      show (0 : Fin 5) ≠ 2 by decide, false_and, if_false, ite_self] using ht
  · simpa only [wordAt_iff, kt_registerFrame, kt_at,
      Function.update_of_ne (show (1 : Fin 5) ≠ 0 by decide), ite_apply, wordWrite_apply,
      show (1 : Fin 5) ≠ 2 by decide, false_and, if_false, ite_self] using hk
  · cases write with
    | false =>
      simpa only [wordAt_iff, kt_registerFrame, kt_at, Bool.false_eq_true, if_false,
        Function.update_of_ne (show (2 : Fin 5) ≠ 0 by decide)] using hw
    | true =>
      simpa only [wordAt_iff, kt_registerFrame, kt_at, if_true,
        Function.update_of_ne (show (2 : Fin 5) ≠ 0 by decide)] using
          kt_wordWrite_word d 2 w v hw hlen.symm
  · simpa only [wordAt_iff, kt_registerFrame, kt_at,
      Function.update_of_ne (show (3 : Fin 5) ≠ 0 by decide), ite_apply, wordWrite_apply,
      show (3 : Fin 5) ≠ 2 by decide, false_and, if_false, ite_self] using hs
  · cases write <;> simp only [Bool.false_eq_true, if_false, if_true, hlen]

/-- The lookup endpoint keeps an already found register, or writes the supplied result
when searching was still active at this suffix. -/
private def kt_lookupPost {x : List Bool} (found : Bool) (d : Cfg 5 Bool kt_TableState x)
    (result : List Bool) (o : ℤ) : Cfg 5 Bool kt_TableState x :=
  kt_at (if found then d else { d with workTapes := wordWrite d 2 result }) ⟨.done, false⟩ o

/-- A suffix endpoint composes with one conditional lookup copy. Once a value was found,
no later entry writes, and an actual copy supplies the final result immediately. -/
private theorem kt_lookupPost_frame {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (found write : Bool) (v tail : List Bool) (q : kt_TableState) (h o : ℤ)
    (hf : found = true → write = false) :
    kt_lookupPost (found || write) (kt_registerFrame d write v q h) tail o =
      kt_lookupPost found d (if write then v else tail) o := by
  cases found with
  | false =>
    cases write with
    | false =>
      change kt_at { kt_at d q h with workTapes := wordWrite (kt_at d q h) 2 tail } ⟨.done, false⟩ o =
        kt_at { d with workTapes := wordWrite d 2 tail } ⟨.done, false⟩ o
      rw [kt_wordWrite_at_other d q h 2 (of_decide_eq_true rfl) tail]
      simp only [kt_at, Function.update_idem]
    | true =>
      exact kt_at_at { d with workTapes := wordWrite d 2 v } q ⟨.done, false⟩ h o
  | true =>
    have hm := hf rfl
    subst write
    exact kt_at_at d q ⟨.done, false⟩ h o

/-- The mathematical first-match lookup composes with a completed entry frame.

**Proof sketch.** `kt_lookupPost_frame` discards any suffix result once a copy has occurred.
The register width is unchanged. If searching was already finished the endpoint ignores its
result argument; otherwise `kt_keyLookup_cons` distinguishes a matching key from a mismatch. -/
private theorem kt_lookupPost_cons {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (found : Bool) (u v k w : List Bool) (tail : List (List Bool × List Bool))
    (q : kt_TableState) (h o : ℤ) (hlen : v.length = w.length) :
    kt_lookupPost (found || kt_match false found u k)
      (kt_registerFrame d (kt_match false found u k) v q h)
      ((keyLookup tail k).getD
        (List.replicate (if kt_match false found u k then v else w).length false)) o =
    kt_lookupPost found d ((keyLookup ((u, v) :: tail) k).getD (List.replicate w.length false)) o := by
  have hwidth : (if kt_match false found u k then v else w).length = w.length := by
    cases hm : kt_match false found u k <;> simp only [Bool.false_eq_true, if_false, if_true, hlen]
  rw [hwidth, kt_lookupPost_frame d found (kt_match false found u k) v _ q h o]
  · cases found with
    | true => rfl
    | false =>
      by_cases heq : u = k <;> simp [kt_match, kt_keyLookup_cons, heq]
  · intro hf
    subst found
    rfl

/-- At the blank pair after the table, lookup either keeps the found word or writes zeros,
then returns to the origin within the layout length plus twice the register width plus fifteen.

**Proof sketch.** The blank tail in `KeyTableAt` supplies the empty word for the final
inspection. A found value dispatches directly to `kt_rewind_run`. Otherwise `kt_zero_run`
overwrites only tape 2, so the table's framed layout survives and the same rewind applies.
Concatenate the three exact runs with `Turing.MultiTapeTM.runFrom_add`. -/
private theorem kt_lookup_end_run {x : List Bool} (found : Bool) (o : ℤ)
    (es : List (List Bool × List Bool)) (w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨.inspect found, .run⟩)
    (hpos : d.workTapePos 0 = o + (keyTableLength es : ℤ) + 1)
    (ht : KeyTableAt d 0 o es) (hw : WordAt d 2 w) (hs : WordAt d 3 []) :
    ∃ t ≤ keyTableLength es + 2 * w.length + 15, (kt_tableTM false).runFrom d t =
      kt_lookupPost found d (List.replicate w.length false) o := by
  have hframe := (keyTableAt_iff _ _ _ _).mp ht
  have hempty : WordAt d 0 [] := by
    rw [wordAt_iff]
    intro z hz _
    rw [FinTM.bufferTape_nil]
    exact hframe.2 (d.workTapePos 0 + z) (by rw [hpos]; omega)
  have hi := kt_inspect_run false found [] d hd hempty hs
  cases found with
  | false =>
    let c : Cfg 5 Bool kt_TableState x := { d with state := some ⟨.zero, .fwd ()⟩ }
    let e : Cfg 5 Bool kt_TableState x :=
      { d with
        state := some ⟨.rewind, .inl .run⟩
        workTapes := wordWrite d 2 (List.replicate w.length false) }
    have hi' : (kt_tableTM false).runFrom d 3 = c := by
      simpa only [kt_tableRedirect, if_true, Bool.false_eq_true, if_false, c] using hi
    have hz : (kt_tableTM false).runFrom c (2 * w.length + 3) = e := by
      simpa only [c, e, kt_wordWrite_state] using kt_zero_run false w c rfl
        (by simpa only [wordAt_iff, c] using hw)
    have heT : TableAt e 0 o [true] (keyFields es) := by
      simpa only [tableAt_iff, e, wordWrite_apply, show (0 : Fin 5) ≠ 2 by decide,
        false_and, if_false] using hframe.1
    have hr := kt_rewind_run false o es e rfl hpos heT
    refine ⟨3 + (2 * w.length + 3 + (keyTableLength es + 9)), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hi', MultiTapeTM.runFrom_add, hz, hr]
    rfl
  | true =>
    let c : Cfg 5 Bool kt_TableState x := { d with state := some ⟨.rewind, .inl .run⟩ }
    have hi' : (kt_tableTM false).runFrom d 3 = c := by
      simpa only [kt_tableRedirect, if_true, Bool.false_eq_true, if_false, c] using hi
    have hcT : TableAt c 0 o [true] (keyFields es) := by simpa only [tableAt_iff, c] using hframe.1
    have hr := kt_rewind_run false o es c rfl hpos hcT
    refine ⟨3 + (keyTableLength es + 9), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hi', hr]
    rfl

/-- Lookup from any entry offset reaches its final result with a linear bound in the
remaining layout, the complete rewind, and the register width.

**Proof sketch.** Induct on `es.drop j`. The empty suffix is `kt_lookup_end_run`.
For a nonempty suffix, expose its first entry using `List.drop_eq_getElem_cons`, read its
marked fields with `kt_table_key_word` and `kt_table_value_word`, and run the one shared
`kt_entry_run`. `kt_registerFrame_invariants` supplies the next suffix's precondition, and
`kt_lookupPost_cons` identifies its first-match result. The successor offset formula makes
the entry cost telescope against the remaining layout length. -/
private theorem kt_lookup_suffix_run {x : List Bool} (o : ℤ)
    (es : List (List Bool × List Bool)) (k : List Bool) (j : ℕ) (found : Bool)
    (w : List Bool) (d : Cfg 5 Bool kt_TableState x) (hj : j ≤ es.length)
    (hd : d.state = some ⟨.inspect found, .run⟩)
    (hpos : d.workTapePos 0 = o + tableOffset [true] (keyFields es) j)
    (ht : KeyTableAt d 0 o es) (hk : WordAt d 1 k) (hw : WordAt d 2 w) (hs : WordAt d 3 [])
    (hwidth : ∀ a ∈ es, a.2.length = w.length) :
    ∃ t ≤ 8 * (keyTableLength es + 1 - tableOffset [true] (keyFields es) j) +
        keyTableLength es + 2 * w.length + 15,
      (kt_tableTM false).runFrom d t =
        kt_lookupPost found d ((keyLookup (es.drop j) k).getD (List.replicate w.length false)) o := by
  generalize htail : es.drop j = tail
  induction tail generalizing j found w d with
  | nil =>
    have hjEq : j = es.length := Nat.le_antisymm hj (List.drop_eq_nil_iff.mp htail)
    subst j
    have hp : d.workTapePos 0 = o + (keyTableLength es : ℤ) + 1 := by
      rw [(kt_tableOffset_endpoints es).2] at hpos
      omega
    have hr := kt_lookup_end_run found o es w d hd hp ht hw hs
    simpa only [(kt_tableOffset_endpoints es).2, Nat.sub_self, mul_zero, zero_add,
      keyLookup_def, List.find?_nil, Option.map_none, Option.getD_none] using hr
  | cons a tail ih =>
    have hjlt : j < es.length := by
      apply Nat.lt_of_not_ge
      intro hge
      have hnil := List.drop_eq_nil_of_le hge
      rw [htail] at hnil
      exact List.cons_ne_nil _ _ hnil
    have hparts : es[j] = a ∧ es.drop (j + 1) = tail :=
      List.cons.inj ((List.drop_eq_getElem_cons hjlt).symm.trans htail)
    have htable := (keyTableAt_iff _ _ _ _).mp ht |>.1
    have hu := kt_table_key_word d 0 o es htable j hjlt hpos
    let c := kt_at d ⟨.copyValue, .inl false⟩ (d.workTapePos 0 + (true :: es[j].1).length + 1)
    have hcT : TableAt c 0 o [true] (keyFields es) := by
      simpa only [tableAt_iff, c, kt_at] using htable
    have hcpos : c.workTapePos 0 = o + tableOffset [true] (keyFields es) j + es[j].1.length + 2 := by
      simp only [c, kt_at, Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hpos]
      omega
    have hv := kt_table_value_word c 0 o es hcT j hjlt hcpos
    have hvlen := hwidth es[j] (List.getElem_mem hjlt)
    obtain ⟨te, hte, hre⟩ := kt_entry_run false found es[j].1 es[j].2 k w d hd hu hv hk hw hs hvlen
    let matched := kt_match false found es[j].1 k
    let q : kt_TableState := ⟨.inspect (found || matched), .run⟩
    let next := o + tableOffset [true] (keyFields es) (j + 1)
    let e := kt_registerFrame d matched es[j].2 q next
    let w' := if matched then es[j].2 else w
    have hhead : d.workTapePos 0 + (es[j].1.length : ℤ) + es[j].2.length + 4 = next := by
      rw [hpos]
      simp only [next, kt_tableOffset_succ es j hjlt, Nat.cast_add, Nat.cast_ofNat]
      omega
    have heRun : (kt_tableTM false).runFrom d te = e := by
      rw [hre, kt_entryPost_lookup, hhead]
      rfl
    have hinv := kt_registerFrame_invariants d matched es[j].2 w k q next o es ht hk hw hs hvlen
    have hepos : e.workTapePos 0 = o + tableOffset [true] (keyFields es) (j + 1) := by
      simp only [e, kt_registerFrame, kt_at, Function.update_self, next]
    have hwidth' : ∀ b ∈ es, b.2.length = w'.length := by
      intro b hb
      exact (hwidth b hb).trans hinv.2.2.2.2.symm
    obtain ⟨tt, htt, hrt⟩ := ih (j := j + 1) (found := found || matched) (w := w') (d := e)
      (by omega) rfl hepos hinv.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2.1 hwidth' hparts.2
    have hpost := kt_lookupPost_cons d found es[j].1 es[j].2 k w tail q next o hvlen
    have hpair : (es[j].1, es[j].2) = a := hparts.1
    rw [hpair] at hpost
    refine ⟨te + tt, ?_, ?_⟩
    · have hsucc := kt_tableOffset_succ es j hjlt
      have hnext := kt_tableOffset_le_end es (j + 1)
      rw [hinv.2.2.2.2] at htt
      omega
    · rw [MultiTapeTM.runFrom_add, heRun, hrt]
      exact hpost

/-- A globally blank scratch tape supplies the empty word used by the end inspection. -/
private theorem kt_scratch_word {x : List Bool} (d : Cfg 5 Bool kt_TableState x)
    (hs : ScratchBlank d) : WordAt d 3 [] := by
  rw [wordAt_iff]
  intro z _ _
  rw [FinTM.bufferTape_nil]
  exact (scratchBlank_iff _).mp hs 3 (by decide) _

/-- Both table operations cross the header in three steps, preserving the complete table
and the query, register and blank scratch words.

**Proof sketch.** `kt_table_header_word` supplies the one-cell header to the shared
`kt_skip_run`. Its framed endpoint changes only the table head and control; the public
word and table readers therefore preserve all stored data. This one preparation is shared
by lookup and assignment. -/
private theorem kt_start_run {x : List Bool} (assign : Bool) (o : ℤ)
    (es : List (List Bool × List Bool)) (k w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨.start, .run⟩) (hpos : d.workTapePos 0 = o)
    (ht : KeyTableAt d 0 o es) (hk : WordAt d 1 k) (hw : WordAt d 2 w) (hs : ScratchBlank d) :
    let c := kt_at d ⟨.inspect false, .run⟩ (o + 2)
    (kt_tableTM assign).runFrom d 3 = c ∧ KeyTableAt c 0 o es ∧
      WordAt c 1 k ∧ WordAt c 2 w ∧ WordAt c 3 [] := by
  let c := kt_at d ⟨.inspect false, .run⟩ (o + 2)
  have hheader := kt_table_header_word d 0 o es ((keyTableAt_iff _ _ _ _).mp ht).1 hpos
  have hstart := kt_skip_run assign .start [true] d hd
    (fun z hz hz' => (wordAt_iff _ _ _).mp hheader z (by omega) hz')
  have hhead : d.workTapePos 0 + (([true] : List Bool).length : ℤ) + 1 = o + 2 := by
    simp only [List.length_cons, List.length_nil, hpos]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [kt_afterSkip, hhead, c] using hstart
  · simpa only [keyTableAt_iff, tableAt_iff, c, kt_at] using ht
  · simpa only [wordAt_iff, c, kt_at, Function.update_of_ne (show (1 : Fin 5) ≠ 0 by decide)] using hk
  · simpa only [wordAt_iff, c, kt_at, Function.update_of_ne (show (2 : Fin 5) ≠ 0 by decide)] using hw
  · simpa only [wordAt_iff, c, kt_at, Function.update_of_ne (show (3 : Fin 5) ≠ 0 by decide)] using
      kt_scratch_word d hs

/-- The lookup controller's complete run has the required register result and a uniform
linear time bound, before packaging its first-exit and radius clauses.

**Proof sketch.** `kt_start_run` crosses the header and supplies the preserved data at
initial entry offset two. Apply `kt_lookup_suffix_run` with found flag false; its
register frame preserves all non-table heads. `kt_wordWrite_at_other` and the function-update equations collapse
the initial framing, and the final table head is the original origin. The suffix bound plus
three header steps is below the uniform constant sixty-four. -/
private theorem kt_lookup_run_within {x : List Bool} (o : ℤ)
    (es : List (List Bool × List Bool)) (k w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨.start, .run⟩) (hpos : d.workTapePos 0 = o)
    (ht : KeyTableAt d 0 o es) (hk : WordAt d 1 k) (hw : WordAt d 2 w)
    (hwidth : ∀ a ∈ es, a.2.length = w.length) (hs : ScratchBlank d) :
    ∃ t ≤ 64 * (keyTableLength es + k.length + w.length + 1),
      (kt_tableTM false).runFrom d t =
        { d with
          state := some ⟨.done, false⟩
          workTapes := wordWrite d 2 ((keyLookup es k).getD (List.replicate w.length false)) } := by
  let c := kt_at d ⟨.inspect false, .run⟩ (o + 2)
  obtain ⟨hstart', hcT, hck, hcw, hcs⟩ := kt_start_run false o es k w d hd hpos ht hk hw hs
  have hcpos : c.workTapePos 0 = o + tableOffset [true] (keyFields es) 0 := by
    simp only [c, kt_at, Function.update_self, (kt_tableOffset_endpoints es).1, Nat.cast_ofNat]
  obtain ⟨t, htime, hr⟩ := kt_lookup_suffix_run o es k 0 false w c (Nat.zero_le _) rfl
    hcpos hcT hck hcw hcs hwidth
  rw [List.drop_zero] at hr
  let result := (keyLookup es k).getD (List.replicate w.length false)
  have hpost : kt_lookupPost false c result o =
      { d with state := some ⟨.done, false⟩, workTapes := wordWrite d 2 result } := by
    change kt_at { kt_at d ⟨.inspect false, .run⟩ (o + 2) with
      workTapes := wordWrite (kt_at d ⟨.inspect false, .run⟩ (o + 2)) 2 result } ⟨.done, false⟩ o = _
    rw [kt_wordWrite_at_other d _ _ 2 (of_decide_eq_true rfl) result]
    simp only [kt_at, Function.update_idem]
    rw [← hpos, Function.update_eq_self]
  refine ⟨3 + t, ?_, ?_⟩
  · rw [(kt_tableOffset_endpoints es).1] at htime
    omega
  · rw [MultiTapeTM.runFrom_add, hstart', hr, hpost]

/-- After a positive number of steps from the final anchor, the controller is parked at
its distinct true control, so the final false anchor is never revisited.

**Proof sketch.** Tag the Boolean cell leaf by the final phase using the public state-map
field equations. `kt_cellTM_run` takes its false entry to true in one step and
`kt_cellTM_park` keeps that endpoint forever. `Turing.phaseHostTM_run_le` transfers this
entire unredirected final phase to the controller. -/
private theorem kt_done_state {x : List Bool} (assign : Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.done, false⟩)
    (n : ℕ) (hn : 0 < n) :
    ((kt_tableTM assign).runFrom d n).state = some ⟨.done, true⟩ := by
  let c := d.mapState fun _ => false
  have hc : c.state = some false := by simp only [c, Cfg.mapState_state, hd, Option.map_some]
  have htag : c.mapState (Sigma.mk kt_TablePhase.done) = d := by
    refine Cfg.mapState_eq_of_fields c _ d ?_ ?_ ?_ ?_ ?_
    · simp only [c, Cfg.mapState_state, hd, Option.map_some]
    · simp only [c, Cfg.mapState_inputPos]
    · exact kt_mapState_workTapes d _
    · funext j
      rw [Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output]
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
  have hlocal : ((kt_tableParts assign .done).runFrom c (1 + v)).state = some true := by
    change ((kt_cellTM (0 : Fin 5) none 0).runFrom c (1 + v)).state = some true
    rw [MultiTapeTM.runFrom_add, kt_cellTM_run 0 none 0 c hc,
      kt_cellTM_park 0 none 0 (kt_cellPost 0 none 0 c) rfl v]
    rfl
  have h := phaseHostTM_run_le (kt_tableParts assign) ⟨.start, .run⟩ (kt_tableRedirect assign)
    .done c (1 + v) (by intro u hu s hs; rfl) (1 + v) le_rfl
  rw [htag] at h
  have hstate := congrArg (fun e : Cfg 5 Bool kt_TableState x => e.state) h
  simp only [Cfg.mapState_state, hlocal, Option.map_some] at hstate
  exact hstate

/-- Any bounded controller run to the final anchor has the required first-exit and radius
clauses, since the anchor cannot be revisited and heads move at most one cell per step.

**Proof sketch.** An earlier final anchor would, by `kt_done_state` and
`Turing.MultiTapeTM.runFrom_add`, force the actual endpoint to have the distinct parked control.
For every earlier time, `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` bounds displacement
by elapsed time, which is at most the same global bound. -/
private theorem kt_reaches_of_run {x : List Bool} (assign : Bool) (B : ℕ)
    (d e : Cfg 5 Bool kt_TableState x) (he : e.state = some ⟨.done, false⟩)
    (h : ∃ t ≤ B, (kt_tableTM assign).runFrom d t = e) :
    ReachesWithin (kt_tableTM assign) d {some ⟨.done, false⟩} B B e := by
  obtain ⟨t, ht, hr⟩ := h
  rw [reachesWithin_iff]
  refine ⟨t, ht, ?_, ?_, hr⟩
  · intro u hu hmem
    have huState := Set.mem_singleton_iff.mp hmem
    have hpark := kt_done_state assign ((kt_tableTM assign).runFrom d u) huState (t - u) (by omega)
    have hfuture : (kt_tableTM assign).runFrom ((kt_tableTM assign).runFrom d u) (t - u) = e := by
      rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le hu.le]
      exact hr
    rw [hfuture, he] at hpark
    cases hpark
  · intro u hu j
    have hhead := MultiTapeTM.workTapePos_runFrom_mem_Icc (kt_tableTM assign) d u j
    have hB : (u : ℤ) ≤ B := by exact_mod_cast hu.trans ht
    rw [Finset.mem_Icc] at hhead
    rw [abs_le]
    constructor <;> omega

/-! ## Private assignment layout -/

/-- A field layout reads its first field through its delimiter and then reads the remaining
layout at the shifted offset.

**Proof sketch.** `Turing.fieldsTape_field` reads the first field, including its right blank;
negative offsets are blank by the published tape equations. Beyond that blank,
`Turing.fieldsTape_cons_shift` reads the tail, and an empty tail is blank past the singleton
layout's length. -/
private theorem kt_fieldsTape_cons (u : List Bool) (fs : List (List Bool)) (z : ℤ) :
    fieldsTape (u :: fs) z =
      if z ≤ (u.length : ℤ) then FinTM.bufferTape u z else fieldsTape fs (z - u.length - 1) := by
  by_cases hz : z ≤ (u.length : ℤ)
  · rw [if_pos hz]
    by_cases hneg : z < -1
    · rw [fieldsTape_of_neg _ (by omega), FinTM.bufferTape_eq, if_neg (by omega)]
    · have h := fieldsTape_field (u :: fs) 0 (Nat.zero_lt_succ fs.length) z (by omega) hz
      simpa only [fieldOffset_zero, Nat.cast_zero, zero_add, List.getElem_cons_zero] using h
  · rw [if_neg hz]
    cases fs with
    | nil =>
      rw [fieldsTape_nil, fieldsTape_of_length_le [u] (by
        rw [joinFields_singleton, List.length_map]
        omega)]
    | cons v fs =>
      have h := fieldsTape_cons_shift u v fs (z - u.length - 1) (by omega)
      rw [show (u.length : ℤ) + 1 + (z - u.length - 1) = z by omega] at h
      exact h

/-- Appending fields starts their tape at the old layout's end offset; the old first
trailing blank remains the separator, and the new layout starts at the second blank.

**Proof sketch.** Induct over the old field list using `kt_fieldsTape_cons` and the public
successor equation for `fieldOffset`. Before the first field ends both tapes read that field.
Beyond it the induction hypothesis applies at the shifted coordinate. The empty prefix uses
only the published negative-cell equation. -/
private theorem kt_fieldsTape_append (fs gs : List (List Bool)) (z : ℤ) :
    fieldsTape (fs ++ gs) z =
      if z < (fieldOffset fs fs.length : ℤ) then fieldsTape fs z
      else fieldsTape gs (z - fieldOffset fs fs.length) := by
  induction fs generalizing z with
  | nil =>
    simp only [List.nil_append, List.length_nil, fieldOffset_zero, Nat.cast_zero,
      sub_zero, fieldsTape_nil]
    by_cases hz : z < 0
    · rw [if_pos hz]
      exact fieldsTape_of_neg gs hz
    · rw [if_neg hz]
  | cons u fs ih =>
    simp only [List.cons_append, List.length_cons, fieldOffset_cons_succ, Nat.cast_add, Nat.cast_one]
    rw [kt_fieldsTape_cons]
    by_cases hz : z ≤ (u.length : ℤ)
    · rw [if_pos hz, if_pos (by omega), kt_fieldsTape_cons, if_pos hz]
    · rw [if_neg hz, ih]
      by_cases hcut : z < (u.length : ℤ) + 1 + fieldOffset fs fs.length
      · rw [if_pos hcut, kt_fieldsTape_cons, if_neg hz, if_pos (by omega)]
      · rw [if_neg hcut, if_neg (by omega)]
        congr 1
        omega

/-- Replacing one field by an equally long field preserves the complete layout length. -/
private theorem kt_joinFields_replace_length (pre post : List (List Bool)) (u w : List Bool)
    (hlen : u.length = w.length) :
    (joinFields (pre ++ w :: post)).length = (joinFields (pre ++ u :: post)).length := by
  have hne (a : List Bool) : pre ++ a :: post ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    omega
  rw [joinFields_length _ (hne w), joinFields_length _ (hne u)]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
    List.length_append, List.length_cons, hlen]

/-- Replacing one equally sized field changes exactly that field's cell interval.

**Proof sketch.** `kt_fieldsTape_append` isolates the unchanged prefix, then
`kt_fieldsTape_cons` isolates the replaced field. Its interior reads the new buffer, its
right delimiter is blank in both equally sized words, and the remaining suffix has the same
shifted origin. No field-cover or private record-table lemma is needed. -/
private theorem kt_fieldsTape_replace (pre post : List (List Bool)) (u w : List Bool)
    (hlen : u.length = w.length) (z : ℤ) :
    fieldsTape (pre ++ w :: post) z =
      if (fieldOffset pre pre.length : ℤ) ≤ z ∧
          z < (fieldOffset pre pre.length : ℤ) + w.length then
        FinTM.bufferTape w (z - fieldOffset pre pre.length)
      else fieldsTape (pre ++ u :: post) z := by
  let D : ℤ := fieldOffset pre pre.length
  rw [kt_fieldsTape_append]
  by_cases hpre : z < D
  · have hout : ¬(D ≤ z ∧ z < D + w.length) := by omega
    rw [if_pos hpre, if_neg hout, kt_fieldsTape_append, if_pos hpre]
  · rw [if_neg hpre, kt_fieldsTape_cons]
    by_cases hin : z < D + w.length
    · have hcell : D ≤ z ∧ z < D + w.length := by omega
      have hle : z - D ≤ (w.length : ℤ) := by omega
      rw [if_pos hcell, if_pos hle]
    · have hout : ¬(D ≤ z ∧ z < D + w.length) := by omega
      rw [if_neg hout, kt_fieldsTape_append, if_neg hpre, kt_fieldsTape_cons, hlen]
      by_cases hend : z = D + w.length
      · rw [show z - D = (w.length : ℤ) by omega]
        simp only [le_refl, if_true]
        rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos (Int.natCast_nonneg _),
          if_pos (Int.natCast_nonneg _), Int.toNat_natCast,
          List.getElem?_eq_none le_rfl, List.getElem?_eq_none (by omega)]
      · have hle : ¬z - D ≤ (w.length : ℤ) := by omega
        rw [if_neg hle, if_neg hle]

/-- Full field spans add under concatenation, including empty field lists. -/
private theorem kt_fieldSpan_append (fs gs : List (List Bool)) :
    fieldOffset (fs ++ gs) (fs ++ gs).length =
      fieldOffset fs fs.length + fieldOffset gs gs.length := by
  induction fs with
  | nil => simp only [List.nil_append, List.length_nil, fieldOffset_zero, zero_add]
  | cons u fs ih =>
    simp only [List.cons_append, List.length_cons, fieldOffset_cons_succ, ih]
    omega

/-- Split a keyed table into its header-and-prefix fields followed by the suffix fields. -/
private theorem kt_tableFields_append (pre es : List (List Bool × List Bool)) :
    tableFields [true] (keyFields (pre ++ es)) =
      tableFields [true] (keyFields pre) ++ (keyFields es).flatten := by
  simp only [keyFields_def, tableFields_eq, List.map_append, List.flatten_append, List.cons_append]

/-- Keyed table lengths add under concatenation after removing the duplicated header cell. -/
private theorem kt_keyTableLength_append (pre es : List (List Bool × List Bool)) :
    keyTableLength (pre ++ es) + 1 = keyTableLength pre + keyTableLength es := by
  induction pre with
  | nil => rw [List.nil_append, kt_keyTableLength_nil]; omega
  | cons e pre ih =>
    rw [List.cons_append, kt_keyTableLength_cons, kt_keyTableLength_cons]
    omega

/-- A same-width field replacement preserves the framed layout when the new field is
correct and every cell outside that field is preserved.

**Proof sketch.** `kt_fieldsTape_replace` gives the exact interval where the layouts differ,
and `kt_joinFields_replace_length` keeps the framed range unchanged. Inside that interval read
the supplied new word at its shifted coordinate; outside it use the preserved old cell. -/
private theorem kt_layout_replace (a b : ℤ → Option Bool) (o : ℤ)
    (pre post : List (List Bool)) (u w : List Bool) (hlen : u.length = w.length)
    (hold : ∀ z : ℤ, -2 ≤ z → z ≤ ((joinFields (pre ++ u :: post)).length : ℤ) + 1 →
      a (o + z) = fieldsTape (pre ++ u :: post) z)
    (hword : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      b (o + fieldOffset pre pre.length + p) = FinTM.bufferTape w p)
    (hkeep : ∀ q : ℤ, q < o + fieldOffset pre pre.length ∨
        o + fieldOffset pre pre.length + w.length ≤ q → b q = a q) :
    ∀ z : ℤ, -2 ≤ z → z ≤ ((joinFields (pre ++ w :: post)).length : ℤ) + 1 →
      b (o + z) = fieldsTape (pre ++ w :: post) z := by
  intro z hz hz'
  rw [kt_fieldsTape_replace pre post u w hlen]
  rw [kt_joinFields_replace_length pre post u w hlen] at hz'
  let D : ℤ := fieldOffset pre pre.length
  by_cases hin : D ≤ z ∧ z < D + w.length
  · rw [if_pos hin]
    have hc := hword (z - D) (by omega) (by omega)
    rw [show o + D + (z - D) = o + z by omega] at hc
    exact hc
  · rw [if_neg hin, hkeep (o + z) (by omega)]
    exact hold z hz hz'

/-- The next entry after a prefix starts at the prefix table's second trailing blank. -/
private theorem kt_tableOffset_prefix (pre es : List (List Bool × List Bool)) :
    tableOffset [true] (keyFields (pre ++ es)) pre.length = keyTableLength pre + 1 := by
  rw [← (kt_tableOffset_endpoints pre).2,
    tableOffset_eq [true] (keyFields (pre ++ es)) (kt_entries_ne_nil (pre ++ es)) pre.length,
    tableOffset_eq [true] (keyFields pre) (kt_entries_ne_nil pre) pre.length]
  simp only [keyFields_def, ← List.map_take, List.take_left, List.take_length]

/-- The fields preceding the current value: header, processed entries, and its marked key. -/
private def kt_valuePrefix (pre : List (List Bool × List Bool)) (k : List Bool) : List (List Bool) :=
  tableFields [true] (keyFields pre) ++ [true :: k]

/-- Isolate the current marked value between its prefix fields and the remaining entries. -/
private theorem kt_tableFields_value (pre es : List (List Bool × List Bool)) (k u : List Bool) :
    tableFields [true] (keyFields (pre ++ (k, u) :: es)) =
      kt_valuePrefix pre k ++ (true :: u) :: (keyFields es).flatten := by
  rw [kt_tableFields_append]
  simp only [kt_valuePrefix, keyFields_def, List.map_cons, List.flatten_cons,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The current value begins after the processed table, its separator and the marked key. -/
private theorem kt_valuePrefix_span (pre : List (List Bool × List Bool)) (k : List Bool) :
    fieldOffset (kt_valuePrefix pre k) (kt_valuePrefix pre k).length =
      keyTableLength pre + k.length + 3 := by
  have hfs : tableFields [true] (keyFields pre) ≠ [] := by
    rw [tableFields_eq]
    exact List.cons_ne_nil _ _
  dsimp only [kt_valuePrefix]
  rw [kt_fieldSpan_append, fieldOffset_length _ hfs, ← keyTableLength_def]
  simp only [List.length_cons, List.length_nil, fieldOffset_cons_succ, fieldOffset_zero]
  omega

/-- The end of an equally sized assigned value lies within the current full table. -/
private theorem kt_valueField_bound (pre post : List (List Bool × List Bool)) (k u w : List Bool)
    (hlen : u.length = w.length) :
    keyTableLength pre + k.length + w.length + 4 ≤ keyTableLength (pre ++ (k, u) :: post) := by
  have hfull := kt_keyTableLength_append pre ((k, u) :: post)
  rw [kt_keyTableLength_cons] at hfull
  change keyTableLength (pre ++ (k, u) :: post) + 1 =
    keyTableLength pre + (k.length + u.length + 4 + keyTableLength post) at hfull
  have htail := kt_tableOffset_le_end post 0
  rw [(kt_tableOffset_endpoints post).1] at htail
  omega

/-- A same-width assignment into a value payload yields the corresponding keyed table,
with unchanged layout length and a still-blank tail.

**Proof sketch.** Isolate the value field with `kt_tableFields_value` and locate it with
`kt_valuePrefix_span`. `kt_markerWrite_word` gives the new delimited marked value, and the
write preserves every cell outside that field. `kt_layout_replace` therefore gives the new
framed table. The field span is within the old layout, so the preserved blank tail starts at
the same position; `kt_joinFields_replace_length` proves equality of the two layout lengths. -/
private theorem kt_assignValue_table {x : List Bool}
    (pre post : List (List Bool × List Bool)) (k u w : List Bool) (o : ℤ)
    (d : Cfg 5 Bool kt_TableState x)
    (hpos : d.workTapePos 0 = o + keyTableLength pre + k.length + 3)
    (ht : KeyTableAt d 0 o (pre ++ (k, u) :: post))
    (hu : WordAt d 0 (true :: u)) (hlen : u.length = w.length) :
    KeyTableAt { d with workTapes := kt_markerWrite d 0 0 w } 0 o (pre ++ (k, w) :: post) ∧
      keyTableLength (pre ++ (k, w) :: post) = keyTableLength (pre ++ (k, u) :: post) := by
  let pf := kt_valuePrefix pre k
  let sf := (keyFields post).flatten
  let e : Cfg 5 Bool kt_TableState x := { d with workTapes := kt_markerWrite d 0 0 w }
  have hmlen : (true :: u).length = (true :: w).length := by simp only [List.length_cons, hlen]
  have hp : d.workTapePos 0 = o + (fieldOffset pf pf.length : ℤ) := by
    change d.workTapePos 0 = o + (fieldOffset (kt_valuePrefix pre k) (kt_valuePrefix pre k).length : ℤ)
    rw [kt_valuePrefix_span]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    omega
  have hL : keyTableLength (pre ++ (k, w) :: post) = keyTableLength (pre ++ (k, u) :: post) := by
    rw [keyTableLength_def, keyTableLength_def, kt_tableFields_value, kt_tableFields_value]
    exact kt_joinFields_replace_length _ _ _ _ hmlen
  have hold : ∀ z : ℤ, -2 ≤ z → z ≤ ((joinFields (pf ++ (true :: u) :: sf)).length : ℤ) + 1 →
      d.workTapes 0 (o + z) = fieldsTape (pf ++ (true :: u) :: sf) z := by
    have h := (tableAt_iff _ _ _ _ _).mp ((keyTableAt_iff _ _ _ _).mp ht).1
    simpa only [kt_tableFields_value] using h
  have hword : ∀ p : ℤ, 0 ≤ p → p ≤ ((true :: w).length : ℤ) →
      e.workTapes 0 (o + fieldOffset pf pf.length + p) = FinTM.bufferTape (true :: w) p := by
    intro p hp0 hp'
    have h := (wordAt_iff _ _ _).mp (kt_markerWrite_word d 0 u w hu hlen) p (by omega) hp'
    change e.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (true :: w) p at h
    rw [hp] at h
    exact h
  have hkeep : ∀ q : ℤ, q < o + fieldOffset pf pf.length ∨
      o + fieldOffset pf pf.length + (true :: w).length ≤ q → e.workTapes 0 q = d.workTapes 0 q := by
    intro q hq
    change kt_markerWrite d 0 0 w 0 q = d.workTapes 0 q
    rw [kt_markerWrite, wordWrite_apply]
    simp only [Function.update_self, true_and]
    rw [if_neg (by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hq
      omega)]
  have htn : TableAt e 0 o [true] (keyFields (pre ++ (k, w) :: post)) := by
    rw [tableAt_iff, kt_tableFields_value]
    exact kt_layout_replace (d.workTapes 0) (e.workTapes 0) o pf sf (true :: u) (true :: w)
      hmlen hold hword hkeep
  have hbound : fieldOffset pf pf.length + (true :: w).length ≤ keyTableLength (pre ++ (k, u) :: post) := by
    have h := kt_valueField_bound pre post k u w hlen
    simp only [pf, kt_valuePrefix_span, List.length_cons]
    omega

  refine ⟨?_, hL⟩
  rw [keyTableAt_iff]
  refine ⟨htn, ?_⟩
  intro q hq
  rw [hL] at hq
  have hbZ : (fieldOffset pf pf.length : ℤ) + ((true :: w).length : ℤ) ≤
      (keyTableLength (pre ++ (k, u) :: post) : ℤ) := by exact_mod_cast hbound
  rw [hkeep q (Or.inr (by omega))]
  exact ((keyTableAt_iff _ _ _ _).mp ht).2 q hq

/-- The first unprocessed entry exposes its marked key and value at the two traversal heads.

**Proof sketch.** `kt_tableOffset_prefix` identifies entry index `pre.length` with the
processed prefix's end. The public key/value field corollaries then read that entry; the
auxiliary value configuration changes only the table head. -/
private theorem kt_prefix_entry_words {x : List Bool}
    (pre es : List (List Bool × List Bool)) (u v : List Bool) (o : ℤ)
    (d : Cfg 5 Bool kt_TableState x)
    (ht : TableAt d 0 o [true] (keyFields (pre ++ (u, v) :: es)))
    (hpos : d.workTapePos 0 = o + keyTableLength pre + 1) :
    WordAt d 0 (true :: u) ∧
      WordAt (kt_at d ⟨.copyValue, .inl false⟩
        (d.workTapePos 0 + (true :: u).length + 1)) 0 (true :: v) := by
  let full := pre ++ (u, v) :: es
  have hj : pre.length < full.length := by simp only [full, List.length_append, List.length_cons]; omega
  have hget : full[pre.length] = (u, v) := by
    simp only [full, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
  have hp0 : d.workTapePos 0 = o + tableOffset [true] (keyFields full) pre.length := by
    simp only [full, kt_tableOffset_prefix, Nat.cast_add, Nat.cast_one]
    omega
  constructor
  · simpa only [hget] using kt_table_key_word d 0 o full ht pre.length hj hp0
  · let c := kt_at d ⟨.copyValue, .inl false⟩ (d.workTapePos 0 + (true :: u).length + 1)
    have hcT : TableAt c 0 o [true] (keyFields full) := by
      simpa only [tableAt_iff, c, kt_at] using ht
    have hp1 : c.workTapePos 0 = o + tableOffset [true] (keyFields full) pre.length + full[pre.length].1.length + 2 := by
      simp only [c, kt_at, Function.update_self, hget, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hp0]
      omega
    simpa only [hget] using kt_table_value_word c 0 o full hcT pre.length hj hp1


/-- Assignment's shared entry endpoint copies the register into exactly the matched value
payload and carries the found flag to the next entry. -/
private theorem kt_entryPost_assign {x : List Bool} (found : Bool) (u v k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) :
    kt_entryPost true found u v k w d =
      kt_at { d with workTapes := if decide (u = k) then
          kt_markerWrite (kt_at d ⟨.copyValue, .inl false⟩
            (d.workTapePos 0 + (true :: u).length + 1)) 0 0 w else d.workTapes }
        ⟨.inspect (found || decide (u = k)), .run⟩
        (d.workTapePos 0 + u.length + v.length + 4) := by
  rw [kt_entryPost_frame]
  have hm : kt_match true found u k = decide (u = k) := by simp only [kt_match, Bool.true_or, Bool.true_and]
  rw [hm]
  simp only [kt_valueWrite, kt_copyDst, if_true]

/-- The footprint of a rewrite contained in the current table interval. -/
private def kt_tableFootprint (o : ℤ) (L : ℕ) (j : Fin 5) : Set ℤ :=
  if j = 0 then Set.Ico o (o + L) else ∅

/-- A complete table write absorbs any earlier rewrite within a contained table footprint.

**Proof sketch.** Inside the final table interval both writers use the same layout cells.
Outside it, the larger final interval contains the earlier footprint, so the public
`Cfg.sameOutside_iff` reader gives equality of the old source cells. -/
private theorem kt_keyTableWrite_frame {S U : Type} {x : List Bool}
    (d : Cfg 5 Bool S x) (e : Cfg 5 Bool U x) (o : ℤ)
    (es : List (List Bool × List Bool)) (L : ℕ) (hle : L ≤ keyTableLength es)
    (hf : Cfg.SameOutside (kt_tableFootprint o L) d e) :
    keyTableWrite e 0 o es = keyTableWrite d 0 o es := by
  funext j q
  rw [keyTableWrite_apply, keyTableWrite_apply]
  by_cases hin : j = 0 ∧ o ≤ q ∧ q < o + keyTableLength es
  · rw [if_pos hin, if_pos hin]
  · rw [if_neg hin, if_neg hin]
    apply (Cfg.sameOutside_iff _ _ _).mp hf j q
    by_cases hj : j = 0
    · subst j
      simp only [kt_tableFootprint, if_true, Set.mem_Ico]
      intro hq
      apply hin
      have hL : (L : ℤ) ≤ keyTableLength es := by exact_mod_cast hle
      exact ⟨rfl, hq.1, by omega⟩
    · simp only [kt_tableFootprint, hj, if_false, Set.mem_empty_iff_false, not_false_eq_true]

/-- A word on another tape survives a table rewrite, by the public stored-word frame rule. -/
private theorem kt_wordAt_tableFrame {S U : Type} {x : List Bool}
    (d : Cfg 5 Bool S x) (e : Cfg 5 Bool U x) (o : ℤ) (L : ℕ)
    (hf : Cfg.SameOutside (kt_tableFootprint o L) d e) (r : Fin 5) (hr : r ≠ 0)
    (hhead : e.workTapePos r = d.workTapePos r) (w : List Bool) (hw : WordAt d r w) :
    WordAt e r w := by
  rw [wordAt_iff, hhead]
  apply hf.keep_word r (d.workTapePos r) w
  · intro p hp hp'
    simp only [kt_tableFootprint, if_neg hr, Set.mem_empty_iff_false, not_false_eq_true]
  · exact (wordAt_iff _ _ _).mp hw

/-- An assignment entry writes only within the original table interval, preserving every
other cell of every tape.

**Proof sketch.** `kt_entryPost_assign` identifies the exact conditional value overwrite.
A mismatch preserves all cells. A match writes only tape 0 between the value payload's start
and end; `kt_valueField_bound` places that interval inside the full table. Package this
pointwise fact through the public `Cfg.sameOutside_iff` reader. -/
private theorem kt_assignEntry_frame {x : List Bool} (found : Bool)
    (pre post : List (List Bool × List Bool)) (u v k w : List Bool) (o : ℤ)
    (d : Cfg 5 Bool kt_TableState x) (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (hlen : v.length = w.length) :
    Cfg.SameOutside (kt_tableFootprint o (keyTableLength (pre ++ (u, v) :: post))) d
      (kt_entryPost true found u v k w d) := by
  let c := kt_at d ⟨.copyValue, .inl false⟩ (d.workTapePos 0 + (true :: u).length + 1)
  have hcpos : c.workTapePos 0 = o + keyTableLength pre + u.length + 3 := by
    simp only [c, kt_at, Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hpos]
    omega
  have hlo : o ≤ c.workTapePos 0 + 1 := by rw [hcpos]; omega
  have hhi : c.workTapePos 0 + 1 + w.length ≤ o + keyTableLength (pre ++ (u, v) :: post) := by
    have hb := kt_valueField_bound pre post u v w hlen
    have hbZ : ((keyTableLength pre + u.length + w.length + 4 : ℕ) : ℤ) ≤
        keyTableLength (pre ++ (u, v) :: post) := by exact_mod_cast hb
    rw [hcpos]
    push_cast at hbZ
    omega
  rw [Cfg.sameOutside_iff]
  intro j q hq
  rw [kt_entryPost_assign]
  change (if decide (u = k) then kt_markerWrite c 0 0 w else d.workTapes) j q = d.workTapes j q
  by_cases heq : u = k
  · simp only [heq, decide_true, if_true]
    by_cases hj : j = 0
    · subst j
      simp only [kt_tableFootprint, if_true, Set.mem_Ico] at hq
      rw [kt_markerWrite, wordWrite_apply]
      simp only [Function.update_self, true_and]
      rw [if_neg (by omega)]
      simp only [c, kt_at]
    · simp only [kt_markerWrite, wordWrite_apply, hj, false_and, if_false, c, kt_at]
  · simp only [heq, decide_false, Bool.false_eq_true, if_false]

/-- Extending a processed prefix by one entry adds exactly that entry's layout contribution. -/
private theorem kt_keyTableLength_append_single (pre : List (List Bool × List Bool))
    (e : List Bool × List Bool) :
    keyTableLength (pre ++ [e]) = keyTableLength pre + e.1.length + e.2.length + 4 := by
  have h := kt_keyTableLength_append pre [e]
  rw [kt_keyTableLength_cons, kt_keyTableLength_nil] at h
  omega

/-- Processing an assignment entry yields its updated table, with no layout-length change.

**Proof sketch.** A mismatch keeps the table cells. On a match, the canonical value-head
configuration has the same table and the supplied marked value word. Apply
`kt_assignValue_table`, then read the shared entry endpoint through `kt_entryPost_assign`;
its final state and head change none of the established table cells. -/
private theorem kt_assignEntry_table {x : List Bool} (found : Bool)
    (pre post : List (List Bool × List Bool)) (u v k w : List Bool) (o : ℤ)
    (d : Cfg 5 Bool kt_TableState x) (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o (pre ++ (u, v) :: post))
    (hv : WordAt (kt_at d ⟨.copyValue, .inl false⟩
      (d.workTapePos 0 + (true :: u).length + 1)) 0 (true :: v))
    (hlen : v.length = w.length) :
    KeyTableAt (kt_entryPost true found u v k w d) 0 o
        (pre ++ (u, if u = k then w else v) :: post) ∧
      keyTableLength (pre ++ (u, if u = k then w else v) :: post) =
        keyTableLength (pre ++ (u, v) :: post) := by
  let c := kt_at d ⟨.copyValue, .inl false⟩ (d.workTapePos 0 + (true :: u).length + 1)
  have hcT : KeyTableAt c 0 o (pre ++ (u, v) :: post) := by
    simpa only [keyTableAt_iff, tableAt_iff, c, kt_at] using ht
  have hcpos : c.workTapePos 0 = o + keyTableLength pre + u.length + 3 := by
    simp only [c, kt_at, Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hpos]
    omega
  by_cases heq : u = k
  · have hm : decide (u = k) = true := by simp only [heq, decide_true]
    have h := kt_assignValue_table pre post u v w o c hcpos hcT hv hlen
    constructor
    · rw [if_pos heq]
      simpa only [kt_entryPost_assign, hm, if_true, keyTableAt_iff, tableAt_iff, kt_at, c] using h.1
    · rw [if_pos heq]
      exact h.2
  · have hm : decide (u = k) = false := by simp only [heq, decide_false]
    constructor
    · rw [if_neg heq]
      simpa only [kt_entryPost_assign, hm, Bool.false_eq_true, if_false,
        keyTableAt_iff, tableAt_iff, kt_at] using ht
    · rw [if_neg heq]

/-- The complete assignment entry invariant: updated table, found flag, next head, preserved
query/register/scratch words, fixed length, and a bounded cell footprint.

**Proof sketch.** `kt_assignEntry_table` supplies the semantic table and length equality,
and `kt_assignEntry_frame` supplies the cell frame. The shared endpoint fixes every other
head, so `kt_wordAt_tableFrame` applies the public stored-word frame rule to all three words.
The state and advancing table head are the canonical entry-frame fields. -/
private theorem kt_assignEntry_invariants {x : List Bool} (found : Bool)
    (pre post : List (List Bool × List Bool)) (u v k w : List Bool) (o : ℤ)
    (d : Cfg 5 Bool kt_TableState x) (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o (pre ++ (u, v) :: post))
    (hv : WordAt (kt_at d ⟨.copyValue, .inl false⟩
      (d.workTapePos 0 + (true :: u).length + 1)) 0 (true :: v))
    (hk : WordAt d 1 k) (hw : WordAt d 2 w) (hs : WordAt d 3 []) (hlen : v.length = w.length) :
    let e := kt_entryPost true found u v k w d
    e.state = some ⟨.inspect (found || decide (u = k)), .run⟩ ∧
    e.workTapePos 0 = d.workTapePos 0 + u.length + v.length + 4 ∧
    KeyTableAt e 0 o (pre ++ (u, if u = k then w else v) :: post) ∧
    WordAt e 1 k ∧ WordAt e 2 w ∧ WordAt e 3 [] ∧
    keyTableLength (pre ++ (u, if u = k then w else v) :: post) =
      keyTableLength (pre ++ (u, v) :: post) ∧
    Cfg.SameOutside (kt_tableFootprint o (keyTableLength (pre ++ (u, v) :: post))) d e := by
  let e := kt_entryPost true found u v k w d
  have htable := kt_assignEntry_table found pre post u v k w o d hpos ht hv hlen
  have hf := kt_assignEntry_frame found pre post u v k w o d hpos hlen
  have hhead (r : Fin 5) (hr : r ≠ 0) : e.workTapePos r = d.workTapePos r := by
    change (kt_entryPost true found u v k w d).workTapePos r = d.workTapePos r
    rw [kt_entryPost_assign]
    simp only [kt_at, Function.update_of_ne hr]
  refine ⟨?_, ?_, htable.1, ?_, ?_, ?_, htable.2, hf⟩
  · rw [kt_entryPost_assign]
    rfl
  · rw [kt_entryPost_assign]
    simp only [kt_at, Function.update_self]
  · exact kt_wordAt_tableFrame d e o _ hf 1 (of_decide_eq_true rfl)
      (hhead 1 (of_decide_eq_true rfl)) k hk
  · exact kt_wordAt_tableFrame d e o _ hf 2 (of_decide_eq_true rfl)
      (hhead 2 (of_decide_eq_true rfl)) w hw
  · exact kt_wordAt_tableFrame d e o _ hf 3 (of_decide_eq_true rfl)
      (hhead 3 (of_decide_eq_true rfl)) [] hs

/-- The remaining assignment result with a flag recording whether an earlier entry matched.
Every remaining match is updated; an absent key appends only when the flag is still false. -/
private def kt_assignTail (found : Bool) (es : List (List Bool × List Bool))
    (k w : List Bool) : List (List Bool × List Bool) :=
  if found || es.any (fun e => e.1 = k) then
    es.map fun e => if e.1 = k then (k, w) else e
  else es ++ [(k, w)]

/-- At the end of the scan, assignment keeps the table after a match and otherwise appends. -/
private theorem kt_assignTail_nil (found : Bool) (k w : List Bool) :
    kt_assignTail found [] k w = if found then [] else [(k, w)] := by
  simp only [kt_assignTail, List.any_nil, Bool.or_false, List.map_nil, List.nil_append]

/-- Assignment updates the current value and then processes the tail with its match flag. -/
private theorem kt_assignTail_cons (found : Bool) (u v k w : List Bool)
    (es : List (List Bool × List Bool)) :
    kt_assignTail found ((u, v) :: es) k w =
      (u, if u = k then w else v) :: kt_assignTail (found || decide (u = k)) es k w := by
  by_cases hhead : u = k <;> cases found <;>
    cases htail : es.any (fun e => decide (e.1 = k)) <;>
    simp [kt_assignTail, List.any_cons, List.map_cons, hhead, htail]

/-- With no earlier match, the suffix result is exactly the frozen keyed assignment. -/
private theorem kt_assignTail_false (es : List (List Bool × List Bool)) (k w : List Bool) :
    kt_assignTail false es k w = keyAssign es k w := by
  simp only [kt_assignTail, keyAssign_def, Bool.false_or]

/-- Equal-width assignment never shortens the remaining table layout.

**Proof sketch.** Induct on the remaining entries using `kt_assignTail_cons`. Each updated
value has its old width, so `kt_keyTableLength_cons` contributes the same entry length and
the induction hypothesis handles the tail. At the empty suffix, keeping or appending has
length at least the one-cell header. -/
private theorem kt_assignTail_length (found : Bool) (es : List (List Bool × List Bool))
    (k w : List Bool) (hwidth : ∀ a ∈ es, a.2.length = w.length) :
    keyTableLength es ≤ keyTableLength (kt_assignTail found es k w) := by
  revert hwidth
  induction es generalizing found with
  | nil =>
    intro _
    rw [kt_assignTail_nil]
    cases found with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [kt_keyTableLength_nil, kt_keyTableLength_cons, kt_keyTableLength_nil]
      omega
    | true => exact le_rfl
  | cons a es ih =>
    intro hwidth
    rcases a with ⟨u, v⟩
    have hvlen : v.length = w.length := hwidth (u, v) List.mem_cons_self
    have htail := ih (found || decide (u = k))
      (fun a ha => hwidth a (List.mem_cons_of_mem _ ha))
    have hnew : (if u = k then w else v).length = v.length := by split_ifs <;> omega
    rw [kt_assignTail_cons, kt_keyTableLength_cons, kt_keyTableLength_cons]
    change u.length + v.length + 4 + keyTableLength es ≤
      u.length + (if u = k then w else v).length + 4 +
        keyTableLength (kt_assignTail (found || decide (u = k)) es k w)
    rw [hnew]
    omega

/-! ## Private append layout and runs -/

/-- A field layout including its left sentinel and its entire blank right tail. -/
private def kt_fullLayout (a : ℤ → Option Bool) (o : ℤ) (fs : List (List Bool)) : Prop :=
  ∀ z : ℤ, -2 ≤ z → a (o + z) = fieldsTape fs z

/-- A keyed table is exactly its full layout, including the blank tail.

**Proof sketch.** On the finite framed interval use `tableAt_iff`; beyond it use the
blank-tail clause of `keyTableAt_iff` and `fieldsTape_of_length_le`. Conversely the full
layout supplies the frame directly and the same public boundary equation supplies its tail. -/
private theorem kt_keyTableAt_iff_layout {K : ℕ} {S : Type} {x : List Bool}
    (d : Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt d r o es ↔ kt_fullLayout (d.workTapes r) o (tableFields [true] (keyFields es)) := by
  rw [keyTableAt_iff, tableAt_iff]
  constructor
  · intro h z hz
    by_cases hend : z ≤ (keyTableLength es : ℤ) + 1
    · exact h.1 z hz hend
    · rw [h.2 (o + z) (by omega), fieldsTape_of_length_le _ (by
        rw [← keyTableLength_def]; omega)]
  · intro h
    constructor
    · intro z hz _
      exact h z hz
    · intro q hq
      have hz : -2 ≤ q - o := by omega
      have hcell := h (q - o) hz
      rw [add_sub_cancel] at hcell
      rw [hcell, fieldsTape_of_length_le _ (by rw [← keyTableLength_def]; omega)]

/-- Extending a full field layout by one word preserves the old layout and its blank tail.

**Proof sketch.** `kt_fieldsTape_append` splits the result at the old full field span.
Before that span use the unchanged old cells. In the new field use its supplied word;
after its right delimiter both layouts are blank by `fieldsTape_of_length_le`. -/
private theorem kt_fullLayout_append (a b : ℤ → Option Bool) (o : ℤ)
    (fs : List (List Bool)) (hfs : fs ≠ []) (w : List Bool)
    (hold : kt_fullLayout a o fs)
    (hword : ∀ p : ℤ, 0 ≤ p → p ≤ (w.length : ℤ) →
      b (o + fieldOffset fs fs.length + p) = FinTM.bufferTape w p)
    (hkeep : ∀ q : ℤ, q < o + fieldOffset fs fs.length ∨
        o + fieldOffset fs fs.length + w.length ≤ q → b q = a q) :
    kt_fullLayout b o (fs ++ [w]) := by
  have hspan := fieldOffset_length fs hfs
  intro z hz
  rw [kt_fieldsTape_append]
  by_cases hpre : z < (fieldOffset fs fs.length : ℤ)
  · rw [if_pos hpre, hkeep (o + z) (Or.inl (by omega)), hold z hz]
  · rw [if_neg hpre, kt_fieldsTape_cons]
    by_cases hfield : z - (fieldOffset fs fs.length : ℤ) ≤ w.length
    · rw [if_pos hfield]
      have h := hword (z - fieldOffset fs fs.length) (by omega) hfield
      rw [show o + fieldOffset fs fs.length + (z - fieldOffset fs fs.length) = o + z by omega] at h
      exact h
    · rw [if_neg hfield, fieldsTape_nil,
        hkeep (o + z) (Or.inr (by omega)), hold z hz,
        fieldsTape_of_length_le fs (by omega)]

/-- The two fields appended when the search found no matching entry. -/
private inductive kt_NewField where
  | key
  | value

/-- Marker-writing phase for a new field. -/
private def kt_newMarkerPhase : kt_NewField → kt_TablePhase
  | .key => .appendKeyMarker
  | .value => .appendValueMarker

/-- The existing adapted-copy use for a new field. -/
private def kt_newCopyKind : kt_NewField → kt_CopyKind
  | .key => .newKey
  | .value => .newValue

/-- The existing skip use for a newly copied marked field. -/
private def kt_newSkipKind : kt_NewField → kt_SkipKind
  | .key => .newKey
  | .value => .newValue

/-- Install the new field's marker without moving any head. -/
private def kt_markField {x : List Bool} (kind : kt_NewField)
    (d : Cfg 5 Bool kt_TableState x) : Cfg 5 Bool kt_TableState x :=
  { d with
    state := some ⟨kt_copyPhase (kt_newCopyKind kind),
      kt_phaseEntry (kt_copyPhase (kt_newCopyKind kind))⟩
    workTapes := Function.update d.workTapes 0
      (Function.update (d.workTapes 0) (d.workTapePos 0) (some true)) }

/-- Each new-field marker takes two steps, including its dispatch to the adapted copy.

**Proof sketch.** Place the shared `kt_cellContract` in the corresponding marker phase
with `kt_phase_run`. Its one write changes only the marker cell, and the dispatch changes
only the state; the phase binding's public field equations give `kt_markField`. -/
private theorem kt_markField_run {x : List Bool} (kind : kt_NewField)
    (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨kt_newMarkerPhase kind, kt_phaseEntry (kt_newMarkerPhase kind)⟩) :
    (kt_tableTM true).runFrom d 2 = kt_markField kind d := by
  let C : Contract (kt_tableParts true (kt_newMarkerPhase kind))
      (kt_phaseEntry (kt_newMarkerPhase kind)) (kt_tableExits (kt_newMarkerPhase kind)) Unit x :=
    match kind with
    | .key => kt_cellContract 0 (some (some true)) 0 (fun (_ : Unit) _ => True)
    | .value => kt_cellContract 0 (some (some true)) 0 (fun (_ : Unit) _ => True)
  have hp : C.pre () (d.mapState fun _ => kt_phaseEntry (kt_newMarkerPhase kind)) := by
    cases kind <;> trivial
  have h := kt_phase_run true (kt_newMarkerPhase kind) C () d hd hp
  cases kind
  all_goals
    dsimp only [C, kt_newMarkerPhase, kt_cellContract] at h
    refine h.trans ?_
    apply Cfg.ext
    · simp only [Cfg.bindState_state, kt_cellPost, Option.bind_some, kt_tableRedirect,
        kt_markField, kt_copyPhase, kt_newCopyKind, kt_phaseEntry]
    · simp only [Cfg.bindState_inputPos, kt_cellPost, Cfg.mapState_inputPos, kt_markField]
    · funext j q
      simp only [Cfg.bindState_workTapes, kt_cellPost, kt_markField,
        kt_mapState_workTapes, Cfg.mapState_workTapePos]
    · funext j
      by_cases hj : j = 0
      · subst j
        simp only [Cfg.bindState_workTapePos, kt_cellPost, Function.update_self,
          Cfg.mapState_workTapePos, kt_markField, SignType.coe_zero, add_zero]
      · simp only [Cfg.bindState_workTapePos, kt_cellPost, Function.update_of_ne hj,
          Cfg.mapState_workTapePos, kt_markField]
    · simp only [Cfg.bindState_output, kt_cellPost, Cfg.mapState_output, kt_markField]

/-- The copied new field before skipping its marker and payload. -/
private def kt_fieldCopied {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) : Cfg 5 Bool kt_TableState x :=
  { kt_markField kind d with
    state := some (kt_afterCopy (kt_newCopyKind kind))
    workTapes := kt_markerWrite (kt_markField kind d) 0 0 w }

/-- The next phase after writing and crossing one new marked field. -/
private def kt_appendFieldPost {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) : Cfg 5 Bool kt_TableState x :=
  kt_at (kt_fieldCopied kind w d) (kt_afterSkip (kt_newSkipKind kind))
    (d.workTapePos 0 + w.length + 2)

/-- A copied new field has its full marked word whenever its two boundary cells were blank.

**Proof sketch.** Marker placement supplies the true bit while leaving the two boundary
cells fixed. The shared `kt_markerWrite_word_of_bounds` then supplies the marked copied word,
without any assumption that the former payload contained Boolean cells. -/
private theorem kt_fieldCopied_word {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x)
    (hl : d.workTapes 0 (d.workTapePos 0 - 1) = none)
    (hr : d.workTapes 0 (d.workTapePos 0 + w.length + 1) = none) :
    WordAt (kt_fieldCopied kind w d) 0 (true :: w) := by
  have hl' : (kt_markField kind d).workTapes 0 ((kt_markField kind d).workTapePos 0 - 1) = none := by
    simpa only [kt_markField, Function.update_self,
      Function.update_of_ne (show d.workTapePos 0 - 1 ≠ d.workTapePos 0 by omega)] using hl
  have hm : (kt_markField kind d).workTapes 0 ((kt_markField kind d).workTapePos 0) = some true := by
    simp only [kt_markField, Function.update_self]
  have hr' : (kt_markField kind d).workTapes 0
      ((kt_markField kind d).workTapePos 0 + w.length + 1) = none := by
    simpa only [kt_markField, Function.update_self,
      Function.update_of_ne (show d.workTapePos 0 + w.length + 1 ≠ d.workTapePos 0 by omega)] using hr
  have h := kt_markerWrite_word_of_bounds (kt_markField kind d) 0 w hl' hm hr'
  simpa only [wordAt_iff, kt_fieldCopied] using h

/-- Appending one field preserves every cell outside its marker and payload interval.

**Proof sketch.** Marker placement writes only the initial cell. The adapted copy writes
only the following payload interval, and the final skip changes no cell. The public
`wordWrite_apply` equation gives both frame cases directly. -/
private theorem kt_appendField_keep {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (j : Fin 5) (q : ℤ)
    (hq : j ≠ 0 ∨ q < d.workTapePos 0 ∨ d.workTapePos 0 + w.length + 1 ≤ q) :
    (kt_appendFieldPost kind w d).workTapes j q = d.workTapes j q := by
  by_cases hj : j = 0
  · subst j
    have haway : q ≠ d.workTapePos 0 := by
      rcases hq with hn | hb | ha
      · exact (hn rfl).elim
      · omega
      · omega
    have hout : ¬(d.workTapePos 0 + 1 ≤ q ∧ q < d.workTapePos 0 + 1 + w.length) := by
      rcases hq with hn | hb | ha
      · exact (hn rfl).elim
      · omega
      · omega
    simp only [kt_appendFieldPost, kt_at, kt_fieldCopied, kt_markerWrite, wordWrite_apply,
      kt_markField, Function.update_self, true_and, if_neg hout, Function.update_of_ne haway]
  · simp only [kt_appendFieldPost, kt_at, kt_fieldCopied, kt_markerWrite, wordWrite_apply,
      hj, false_and, if_false, kt_markField, Function.update_of_ne hj]

/-- Appending and crossing a marked field takes three times its payload length plus
fourteen steps, with one implementation shared by the new key and value.

**Proof sketch.** `kt_markField_run` installs the marker, `kt_copy_run` copies the source
through the shared adapter, and `kt_fieldCopied_word` supplies the new delimited field for
`kt_skip_run`. The source lies on another tape, so marker opening preserves it. Compose the
three exact runs with `MultiTapeTM.runFrom_add`. -/
private theorem kt_appendField_run {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨kt_newMarkerPhase kind, kt_phaseEntry (kt_newMarkerPhase kind)⟩)
    (hw : WordAt d (kt_copySrc true (kt_newCopyKind kind)) w)
    (hl : d.workTapes 0 (d.workTapePos 0 - 1) = none)
    (hr : d.workTapes 0 (d.workTapePos 0 + w.length + 1) = none) :
    (kt_tableTM true).runFrom d (3 * w.length + 14) = kt_appendFieldPost kind w d := by
  let m := kt_markField kind d
  let e := kt_fieldCopied kind w d
  have hne : kt_copySrc true (kt_newCopyKind kind) ≠ 0 := by cases kind <;> decide
  have hdst : kt_copyDst true (kt_newCopyKind kind) = 0 := by cases kind <;> rfl
  have hsource : WordAt m (kt_copySrc true (kt_newCopyKind kind)) w := by
    simpa only [wordAt_iff, m, kt_markField, Function.update_of_ne hne] using hw
  have hmarker : m.workTapes 0 (m.workTapePos 0) = some true := by
    simp only [m, kt_markField, Function.update_self]
  have hmark := kt_markField_run kind d hd
  have hcopy : (kt_tableTM true).runFrom m (2 * w.length + 9) = e := by
    have h := kt_copy_run true (kt_newCopyKind kind) w m rfl
      (kt_openMarker_word_other m 0 _ hne w hsource) hmarker
    rw [hdst] at h
    exact h
  have heword : WordAt e 0 (true :: w) := kt_fieldCopied_word kind w d hl hr
  have hskip : (kt_tableTM true).runFrom e (w.length + 3) = kt_appendFieldPost kind w d := by
    have h := kt_skip_run true (kt_newSkipKind kind) (true :: w) e
      (by cases kind <;> rfl) (fun p hp hp' => (wordAt_iff _ _ _).mp heword p (by omega) hp')
    simpa only [kt_appendFieldPost, e, kt_fieldCopied, kt_markField,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc] using h
  rw [show 3 * w.length + 14 = 2 + (2 * w.length + 9 + (w.length + 3)) by omega,
    MultiTapeTM.runFrom_add, hmark, MultiTapeTM.runFrom_add, hcopy, hskip]

/-- Appending one marked field extends the complete stored layout, including its blank tail.

**Proof sketch.** The old full layout is blank from its length onward, which supplies both
boundary cells for `kt_fieldCopied_word`. The copied word and `kt_appendField_keep` then
satisfy the shared `kt_fullLayout_append` lemma. Skipping the new field changes only its head. -/
private theorem kt_appendField_layout {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (o : ℤ) (fs : List (List Bool)) (hfs : fs ≠ [])
    (ht : kt_fullLayout (d.workTapes 0) o fs)
    (hpos : d.workTapePos 0 = o + fieldOffset fs fs.length) :
    kt_fullLayout ((kt_appendFieldPost kind w d).workTapes 0) o (fs ++ [true :: w]) := by
  have hspan := fieldOffset_length fs hfs
  have hblank (q : ℤ) (hq : o + (joinFields fs).length ≤ q) : d.workTapes 0 q = none := by
    have h := ht (q - o) (by omega)
    rw [add_sub_cancel] at h
    rw [h, fieldsTape_of_length_le fs (by omega)]
  have heword := kt_fieldCopied_word kind w d
    (hblank (d.workTapePos 0 - 1) (by rw [hpos]; omega))
    (hblank (d.workTapePos 0 + w.length + 1) (by rw [hpos]; omega))
  apply kt_fullLayout_append (d.workTapes 0) _ o fs hfs (true :: w) ht
  · intro p hp hp'
    have h := (wordAt_iff _ _ _).mp heword p (by omega) hp'
    simpa only [kt_appendFieldPost, kt_at, kt_fieldCopied, kt_markField, hpos] using h
  · intro q hq
    apply kt_appendField_keep
    rcases hq with hb | ha
    · exact Or.inr (Or.inl (by rw [hpos]; exact hb))
    · apply Or.inr ∘ Or.inr
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ha
      rw [hpos]
      omega

/-- Appending a field preserves every word stored on another tape, including its head. -/
private theorem kt_appendField_otherWord {x : List Bool} (kind : kt_NewField) (w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (r : Fin 5) (hr : r ≠ 0) (u : List Bool)
    (hu : WordAt d r u) : WordAt (kt_appendFieldPost kind w d) r u := by
  rw [wordAt_iff]
  intro p hp hp'
  have hpos : (kt_appendFieldPost kind w d).workTapePos r = d.workTapePos r := by
    simp only [kt_appendFieldPost, kt_at, kt_fieldCopied, kt_markField, Function.update_of_ne hr]
  rw [hpos, kt_appendField_keep kind w d r _ (Or.inl hr)]
  exact (wordAt_iff _ _ _).mp hu p hp hp'

/-- A framed configuration holding the requested table has exactly the published table-write
tape vector.

**Proof sketch.** Inside the final table interval, `kt_keyTableAt_iff_layout` gives its cells.
Outside that interval, the public `Cfg.sameOutside_iff` frame supplies the original cells.
These are precisely the two branches of `keyTableWrite_apply`. -/
private theorem kt_keyTableWrite_eq {S U : Type} {x : List Bool}
    (d : Cfg 5 Bool S x) (e : Cfg 5 Bool U x) (o : ℤ)
    (es : List (List Bool × List Bool)) (ht : KeyTableAt e 0 o es)
    (hf : Cfg.SameOutside (kt_tableFootprint o (keyTableLength es)) d e) :
    e.workTapes = keyTableWrite d 0 o es := by
  funext j q
  rw [keyTableWrite_apply]
  by_cases hin : j = 0 ∧ o ≤ q ∧ q < o + keyTableLength es
  · rw [if_pos hin]
    rcases hin with ⟨rfl, hlo, _⟩
    have h := (kt_keyTableAt_iff_layout _ _ _ _).mp ht (q - o) (by omega)
    simpa only [add_sub_cancel] using h
  · rw [if_neg hin]
    apply (Cfg.sameOutside_iff _ _ _).mp hf j q
    by_cases hj : j = 0
    · subst j
      simp only [kt_tableFootprint, if_true, Set.mem_Ico]
      intro hq
      exact hin ⟨rfl, hq.1, hq.2⟩
    · simp only [kt_tableFootprint, hj, if_false, Set.mem_empty_iff_false, not_false_eq_true]

/-- The configuration after appending the new key and value, ready for the final rewind. -/
private def kt_appendEntryPost {x : List Bool} (k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) : Cfg 5 Bool kt_TableState x :=
  kt_appendFieldPost .value w (kt_appendFieldPost .key k d)

/-- Two field appends produce the extended keyed table at its new end, with every cell
outside the extended table interval preserved.

**Proof sketch.** Apply `kt_appendField_layout` to the key and then the value. The
intermediate fields are `kt_valuePrefix`, whose span locates the value marker. The final
fields are those of the appended keyed entry. `kt_appendField_keep` composes the two cell
frames, since both write intervals lie in the extended table. The explicit append length
formula identifies the final head with its second trailing blank. -/
private theorem kt_appendEntry_table {x : List Bool} (o : ℤ)
    (pre : List (List Bool × List Bool)) (k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o pre) :
    KeyTableAt (kt_appendEntryPost k w d) 0 o (pre ++ [(k, w)]) ∧
      (kt_appendEntryPost k w d).workTapePos 0 = o + keyTableLength (pre ++ [(k, w)]) + 1 ∧
      Cfg.SameOutside (kt_tableFootprint o (keyTableLength (pre ++ [(k, w)]))) d
        (kt_appendEntryPost k w d) := by
  let c := kt_appendFieldPost .key k d
  let fs := tableFields [true] (keyFields pre)
  have hfs : fs ≠ [] := by
    change tableFields [true] (keyFields pre) ≠ []
    rw [tableFields_eq]
    exact List.cons_ne_nil _ _
  have hcpos : c.workTapePos 0 = o + keyTableLength pre + k.length + 3 := by
    simp only [c, kt_appendFieldPost, kt_at, Function.update_self]
    rw [hpos]
    omega
  have hnew := kt_keyTableLength_append_single pre (k, w)
  change keyTableLength (pre ++ [(k, w)]) = keyTableLength pre + k.length + w.length + 4 at hnew
  have hstart : d.workTapePos 0 = o + fieldOffset fs fs.length := by
    rw [fieldOffset_length fs hfs]
    change d.workTapePos 0 = o + (keyTableLength pre + 1 : ℕ)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hpos
  have hcLayout : kt_fullLayout (c.workTapes 0) o (kt_valuePrefix pre k) :=
    kt_appendField_layout .key k d o fs hfs ((kt_keyTableAt_iff_layout _ _ _ _).mp ht) hstart
  have heLayout := kt_appendField_layout .value w c o (kt_valuePrefix pre k)
    (by simp [kt_valuePrefix]) hcLayout (by
      rw [kt_valuePrefix_span]
      simp only [Nat.cast_add, Nat.cast_ofNat]
      omega)
  have heTable : KeyTableAt (kt_appendEntryPost k w d) 0 o (pre ++ [(k, w)]) := by
    rw [kt_keyTableAt_iff_layout, kt_tableFields_value]
    simpa only [keyFields_def, List.map_nil, List.flatten_nil] using heLayout
  refine ⟨heTable, ?_, ?_⟩
  · change c.workTapePos 0 + w.length + 2 = o + keyTableLength (pre ++ [(k, w)]) + 1
    rw [hcpos, hnew]
    push_cast
    omega
  · rw [Cfg.sameOutside_iff]
    intro j q hq
    change (kt_appendFieldPost .value w c).workTapes j q = d.workTapes j q
    by_cases hj : j = 0
    · subst j
      simp only [kt_tableFootprint, if_true, Set.mem_Ico] at hq
      rw [kt_appendField_keep .value w c 0 q (Or.inr (by rw [hcpos]; rw [hnew] at hq; push_cast at hq; omega)),
        kt_appendField_keep .key k d 0 q (Or.inr (by rw [hpos]; rw [hnew] at hq; push_cast at hq; omega))]
    · rw [kt_appendField_keep .value w c j q (Or.inl hj),
        kt_appendField_keep .key k d j q (Or.inl hj)]

/-- The canonical assignment endpoint: the requested table, original outer frame and heads. -/
private def kt_assignPost {x : List Bool} (d : Cfg 5 Bool kt_TableState x) (o : ℤ)
    (es : List (List Bool × List Bool)) : Cfg 5 Bool kt_TableState x :=
  kt_at { d with workTapes := keyTableWrite d 0 o es } ⟨.done, false⟩ o

/-- Appending the missing entry and rewinding takes the old table length plus four times
each source width plus forty-one steps, with the exact published table-write endpoint.

**Proof sketch.** `kt_appendField_run` writes the key and value in succession. The old blank
tail and `kt_appendField_keep` supply both fields' boundary blanks, while
`kt_appendField_otherWord` preserves the register. `kt_appendEntry_table` establishes the
extended table and final head; its cell frame and `kt_keyTableWrite_eq` identify the exact
tape vector. Finish with `kt_rewind_run`, which restores the table head and leaves all cells. -/
private theorem kt_appendEntry_run {x : List Bool} (o : ℤ)
    (pre : List (List Bool × List Bool)) (k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.appendKeyMarker, false⟩)
    (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o pre) (hk : WordAt d 1 k) (hw : WordAt d 2 w) :
    (kt_tableTM true).runFrom d (keyTableLength pre + 4 * k.length + 4 * w.length + 41) =
      kt_assignPost d o (pre ++ [(k, w)]) := by
  let c := kt_appendFieldPost .key k d
  let e := kt_appendEntryPost k w d
  have hblank (q : ℤ) (hq : d.workTapePos 0 - 1 ≤ q) : d.workTapes 0 q = none :=
    ((keyTableAt_iff _ _ _ _).mp ht).2 q (by rw [hpos] at hq; omega)
  have hkey := kt_appendField_run .key k d hd hk
    (hblank _ le_rfl) (hblank _ (by omega))
  have hcpos : c.workTapePos 0 = d.workTapePos 0 + k.length + 2 := rfl
  have hcblank (q : ℤ) (hq : c.workTapePos 0 - 1 ≤ q) : c.workTapes 0 q = none := by
    rw [kt_appendField_keep .key k d 0 q (Or.inr (Or.inr (by rw [hcpos] at hq; omega))),
      hblank q (by rw [hcpos] at hq; omega)]
  have hvalue : (kt_tableTM true).runFrom c (3 * w.length + 14) = e :=
    kt_appendField_run .value w c rfl
      (kt_appendField_otherWord .key k d 2 (of_decide_eq_true rfl) w hw)
      (hcblank _ le_rfl) (hcblank _ (by omega))
  have he := kt_appendEntry_table o pre k w d hpos ht
  have hr := kt_rewind_run true o (pre ++ [(k, w)]) e rfl he.2.1
    ((keyTableAt_iff _ _ _ _).mp he.1).1
  have htapes := kt_keyTableWrite_eq d e o (pre ++ [(k, w)]) he.1 he.2.2
  have hnew := kt_keyTableLength_append_single pre (k, w)
  change keyTableLength (pre ++ [(k, w)]) = keyTableLength pre + k.length + w.length + 4 at hnew
  rw [show keyTableLength pre + 4 * k.length + 4 * w.length + 41 =
      3 * k.length + 14 + (3 * w.length + 14 + (keyTableLength (pre ++ [(k, w)]) + 9)) by omega,
    MultiTapeTM.runFrom_add, hkey, MultiTapeTM.runFrom_add, hvalue, hr]
  apply Cfg.ext
  · rfl
  · rfl
  · exact htapes
  · funext j
    by_cases hj : j = 0
    · subst j
      simp only [kt_assignPost, kt_at, Function.update_self]
    · simp only [kt_assignPost, kt_at, e, kt_appendEntryPost, kt_appendFieldPost,
        kt_fieldCopied, kt_markField, Function.update_of_ne hj]
  · rfl

/-- At the table's end, assignment rewinds after a previous match or appends the missing
entry, within the table length plus four times each source width plus forty-eight steps.

**Proof sketch.** The blank tail supplies the empty word for `kt_inspect_run`. A true found
flag dispatches to `kt_rewind_run`; the unchanged table already equals its own table write
by `kt_keyTableWrite_eq`. A false flag dispatches to `kt_appendEntry_run`. The state-only
inspection frame changes neither source word nor any cell of the table-write endpoint. -/
private theorem kt_assign_end_run {x : List Bool} (found : Bool) (o : ℤ)
    (pre : List (List Bool × List Bool)) (k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.inspect found, .run⟩)
    (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o pre) (hk : WordAt d 1 k) (hw : WordAt d 2 w)
    (hs : WordAt d 3 []) :
    ∃ t ≤ keyTableLength pre + 4 * k.length + 4 * w.length + 48,
      (kt_tableTM true).runFrom d t = kt_assignPost d o (pre ++ kt_assignTail found [] k w) := by
  have hempty : WordAt d 0 [] := by
    rw [wordAt_iff]
    intro z hz _
    rw [FinTM.bufferTape_nil]
    exact ((keyTableAt_iff _ _ _ _).mp ht).2 (d.workTapePos 0 + z) (by rw [hpos]; omega)
  have hi := kt_inspect_run true found [] d hd hempty hs
  cases found with
  | false =>
    let c : Cfg 5 Bool kt_TableState x := { d with state := some ⟨.appendKeyMarker, false⟩ }
    have hi' : (kt_tableTM true).runFrom d 3 = c := by
      simpa only [kt_tableRedirect, if_true, Bool.false_eq_true, if_false, c] using hi
    have hr := kt_appendEntry_run o pre k w c rfl hpos
      (by simpa only [keyTableAt_iff, tableAt_iff, c] using ht)
      (by simpa only [wordAt_iff, c] using hk)
      (by simpa only [wordAt_iff, c] using hw)
    refine ⟨3 + (keyTableLength pre + 4 * k.length + 4 * w.length + 41), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hi', hr, kt_assignTail_nil]
    rfl
  | true =>
    let c : Cfg 5 Bool kt_TableState x := { d with state := some ⟨.rewind, .inl .run⟩ }
    have hi' : (kt_tableTM true).runFrom d 3 = c := by
      simpa only [kt_tableRedirect, if_true, c] using hi
    have hr := kt_rewind_run true o pre c rfl hpos
      (by simpa only [tableAt_iff, c] using ((keyTableAt_iff _ _ _ _).mp ht).1)
    have hf : Cfg.SameOutside (kt_tableFootprint o (keyTableLength pre)) d d :=
      (Cfg.sameOutside_iff _ _ _).mpr (fun _ _ _ => rfl)
    have hwrite := (kt_keyTableWrite_eq d d o pre ht hf).symm
    refine ⟨3 + (keyTableLength pre + 9), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hi', hr, kt_assignTail_nil]
    simp only [if_true, List.append_nil, kt_assignPost, hwrite, c, kt_at]

/-- Assignment from any processed prefix reaches the all-match update or missing-key append,
with the entry costs telescoping over the remaining layout.

**Proof sketch.** Induct on the unprocessed entries. The empty suffix is
`kt_assign_end_run`. For a current entry, `kt_prefix_entry_words` exposes its two marked
fields, and `kt_entry_run` performs the shared scan. `kt_assignEntry_invariants` supplies the
updated table, found flag, next head, preserved source words and cell frame. Extend the
processed prefix by the updated entry and apply the induction hypothesis. The recurrence
`kt_assignTail_cons` identifies the mathematical result. Since equal-width assignment never
shortens the result, `kt_keyTableWrite_frame` absorbs the earlier payload write. Finally the
entry length formula telescopes the linear time bound. -/
private theorem kt_assign_suffix_run {x : List Bool} (o : ℤ)
    (pre es : List (List Bool × List Bool)) (found : Bool) (k w : List Bool)
    (d : Cfg 5 Bool kt_TableState x) (hd : d.state = some ⟨.inspect found, .run⟩)
    (hpos : d.workTapePos 0 = o + keyTableLength pre + 1)
    (ht : KeyTableAt d 0 o (pre ++ es)) (hk : WordAt d 1 k) (hw : WordAt d 2 w)
    (hs : WordAt d 3 []) (hwidth : ∀ a ∈ es, a.2.length = w.length) :
    ∃ t ≤ 8 * (keyTableLength es - 1) + keyTableLength (pre ++ es) +
        4 * k.length + 4 * w.length + 48,
      (kt_tableTM true).runFrom d t =
        kt_assignPost d o (pre ++ kt_assignTail found es k w) := by
  induction es generalizing pre found d with
  | nil =>
    simpa only [List.append_nil, kt_keyTableLength_nil, Nat.sub_self, mul_zero, zero_add] using
      kt_assign_end_run found o pre k w d hd hpos (by simpa only [List.append_nil] using ht) hk hw hs
  | cons a es ih =>
    rcases a with ⟨u, v⟩
    have hvlen : v.length = w.length := hwidth (u, v) List.mem_cons_self
    have hwords := kt_prefix_entry_words pre es u v o d
      ((keyTableAt_iff _ _ _ _).mp ht).1 hpos
    obtain ⟨te, hte, hre⟩ := kt_entry_run true found u v k w d hd
      hwords.1 hwords.2 hk hw hs hvlen
    let e := kt_entryPost true found u v k w d
    let pre' := pre ++ [(u, if u = k then w else v)]
    have hinv := kt_assignEntry_invariants found pre es u v k w o d hpos ht
      hwords.2 hk hw hs hvlen
    rcases hinv with ⟨hstate, hhead, htable, hkey, hword, hscratch, hlength, hframe⟩
    have hnewlen : (if u = k then w else v).length = v.length := by split_ifs <;> omega
    have hpre := kt_keyTableLength_append_single pre (u, if u = k then w else v)
    change keyTableLength pre' = keyTableLength pre + u.length +
      (if u = k then w else v).length + 4 at hpre
    rw [hnewlen] at hpre
    have hepos : e.workTapePos 0 = o + keyTableLength pre' + 1 := by
      change (kt_entryPost true found u v k w d).workTapePos 0 = _
      rw [hhead, hpos, hpre]
      push_cast
      omega
    have heTable : KeyTableAt e 0 o (pre' ++ es) := by
      simpa only [pre', List.append_assoc, List.cons_append, List.nil_append] using htable
    have hfull : keyTableLength (pre' ++ es) = keyTableLength (pre ++ (u, v) :: es) := by
      simpa only [pre', List.append_assoc, List.cons_append, List.nil_append] using hlength
    have htailWidth : ∀ a ∈ es, a.2.length = w.length :=
      fun a ha => hwidth a (List.mem_cons_of_mem _ ha)
    obtain ⟨tt, htt, hrt⟩ := ih (pre := pre') (found := found || decide (u = k)) (d := e)
      hstate hepos heTable hkey hword hscratch htailWidth
    have hresult : pre' ++ kt_assignTail (found || decide (u = k)) es k w =
        pre ++ kt_assignTail found ((u, v) :: es) k w := by
      simp only [pre', kt_assignTail_cons, List.append_assoc, List.cons_append, List.nil_append]
    have hlenTail := kt_assignTail_length found ((u, v) :: es) k w hwidth
    have hfinal : keyTableLength (pre ++ (u, v) :: es) ≤
        keyTableLength (pre ++ kt_assignTail found ((u, v) :: es) k w) := by
      have h0 := kt_keyTableLength_append pre ((u, v) :: es)
      have h1 := kt_keyTableLength_append pre (kt_assignTail found ((u, v) :: es) k w)
      omega
    have htapes := kt_keyTableWrite_frame d e o
      (pre ++ kt_assignTail found ((u, v) :: es) k w) _ hfinal hframe
    refine ⟨te + tt, ?_, ?_⟩
    · rw [hfull] at htt
      have htailPos := kt_tableOffset_le_end es 0
      rw [(kt_tableOffset_endpoints es).1] at htailPos
      rw [kt_keyTableLength_cons]
      change te + tt ≤ 8 * (u.length + v.length + 4 + keyTableLength es - 1) +
        keyTableLength (pre ++ (u, v) :: es) + 4 * k.length + 4 * w.length + 48
      omega
    · rw [MultiTapeTM.runFrom_add, hre, hrt, hresult]
      apply Cfg.ext
      · rfl
      · simp only [kt_assignPost, kt_at, e, kt_entryPost_assign]
      · exact htapes
      · funext j
        by_cases hj : j = 0
        · subst j
          simp only [kt_assignPost, kt_at, Function.update_self]
        · simp only [kt_assignPost, kt_at, Function.update_of_ne hj, e, kt_entryPost_assign]
      · simp only [kt_assignPost, kt_at, e, kt_entryPost_assign]

/-- The complete assignment run has the frozen table-write endpoint within a uniform
linear time bound.

**Proof sketch.** `kt_start_run` crosses the header and preserves the stored words. Apply
`kt_assign_suffix_run` with empty processed prefix and false found flag, so
`kt_assignTail_false` identifies its result with `keyAssign`. The initial framing changes
no tape cell; the final origin equals the original table head, so the function-update
identities restore the complete original head vector. The suffix bound plus three header
steps is below the uniform constant sixty-four. -/
private theorem kt_assign_run_within {x : List Bool} (o : ℤ)
    (es : List (List Bool × List Bool)) (k w : List Bool) (d : Cfg 5 Bool kt_TableState x)
    (hd : d.state = some ⟨.start, .run⟩) (hpos : d.workTapePos 0 = o)
    (ht : KeyTableAt d 0 o es) (hk : WordAt d 1 k) (hw : WordAt d 2 w)
    (hwidth : ∀ a ∈ es, a.2.length = w.length) (hs : ScratchBlank d) :
    ∃ t ≤ 64 * (keyTableLength es + k.length + w.length + 1),
      (kt_tableTM true).runFrom d t =
        { d with state := some ⟨.done, false⟩, workTapes := keyTableWrite d 0 o (keyAssign es k w) } := by
  let c := kt_at d ⟨.inspect false, .run⟩ (o + 2)
  obtain ⟨hstart, hcT, hck, hcw, hcs⟩ := kt_start_run true o es k w d hd hpos ht hk hw hs
  have hcpos : c.workTapePos 0 = o + keyTableLength [] + 1 := by
    simp only [c, kt_at, Function.update_self, kt_keyTableLength_nil]
    omega
  obtain ⟨t, htime, hr⟩ := kt_assign_suffix_run o [] es false k w c rfl hcpos
    (by simpa only [List.nil_append] using hcT) hck hcw hcs hwidth
  simp only [List.nil_append, kt_assignTail_false] at hr htime
  refine ⟨3 + t, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, hstart, hr]
  have hwrite : keyTableWrite c 0 o (keyAssign es k w) = keyTableWrite d 0 o (keyAssign es k w) := rfl
  change kt_at { c with workTapes := keyTableWrite c 0 o (keyAssign es k w) } ⟨.done, false⟩ o = _
  rw [hwrite]
  simp only [c, kt_at, Function.update_idem]
  rw [← hpos, Function.update_eq_self]

/-! ## The rows

Both rows are five-tape machines over `Bool`: tape `0` holds the table, with its head at the
origin; tape `1` the key; tape `2` the value register; tapes `3` and `4` are blank scratch tapes
(`Turing.ScratchBlank`), left blank. Every head ends where it started. -/

/-- **Keyed lookup.** From the entry, with a keyed table `es` at the head of tape `0`, a key `k`
on tape `1` and a register word `w` on tape `2`, every value of the table as long as `w`, and
blank scratch tapes: the row writes over `w` the value stored under `k`, or `|w|` zeros if `k` is
absent, and stops at its exit within `C·(L + |k| + |w| + 1)` steps and radius, where `L` is the
table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** Instantiate the finite controller `kt_tableTM` in lookup mode.
`kt_markerContract` supplies one shared delimiter adapter for both `Turing.compareTM` and
`Turing.copyTM`, including empty payloads. `kt_lookup_suffix_run` inducts on the unvisited
entries using `kt_entry_run`; a found flag preserves the first matching value while the
remaining fields are skipped. Each entry costs at most eight times its layout contribution,
so the successor-offset formula telescopes the search bound. At the end, `kt_lookup_end_run`
keeps the found register or zeros its original interval and rewinds the table head.
`kt_lookup_run_within` includes the initial header skip and bounds the whole run by the uniform
constant sixty-four. Finally, `kt_reaches_of_run` obtains the first-exit cut from the final
anchor's non-revisit property and the radius from the model's one-cell-per-step head bound. -/
theorem exists_keyLookupTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k w : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 w → (∀ e ∈ es, e.2.length = w.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + w.length + 1))
          (C * (keyTableLength es + k.length + w.length + 1))
          { d with state := some exit,
                   workTapes :=
                     wordWrite d 2 ((keyLookup es k).getD (List.replicate w.length false)) } := by
  classical
  refine ⟨kt_TableState, inferInstance, inferInstance, kt_tableTM false,
    ⟨.start, .run⟩, ⟨.done, false⟩, 64, ?_⟩
  intro x o es k w d hd hpos ht hk hw hwidth hs
  exact kt_reaches_of_run false _ d _ rfl
    (kt_lookup_run_within o es k w d hd hpos ht hk hw hwidth hs)

/-- **Keyed assignment.** From the entry, with a keyed table `es` at the head of tape `0`, a key
`k` on tape `1` and a value `v` on tape `2`, every value of the table as long as `v`, and blank
scratch tapes: the row lays out `keyAssign es k v` from the origin, overwriting the value under
`k` in place or appending `(k, v)`, and stops at its exit within `C·(L + |k| + |v| + 1)` steps
and radius, where `L` is the old table's layout length. [AB09, Exercise 1.9]

**Proof sketch.** Instantiate the shared finite phase controller `kt_tableTM` in assignment
mode. `kt_markerContract` supplies the single delimiter adapter used for comparison and
copying. `kt_assign_suffix_run` scans the remaining entries using `kt_entry_run` and the
complete `kt_assignEntry_invariants`, extending the processed prefix with each updated value
and retaining a found flag. At the end `kt_assign_end_run` rewinds after a match, or uses
`kt_appendEntry_run` to append both marked source words into the blank tail and rewind.
`kt_keyTableWrite_eq` and `kt_keyTableWrite_frame` identify the exact frozen table-write
endpoint. Entry costs telescope, and `kt_assign_run_within` includes the shared header
preparation with uniform constant sixty-four. `kt_reaches_of_run` obtains the first-exit cut
from the final anchor's non-revisit property and the radius from the model's head bound. -/
theorem exists_keyAssignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (o : ℤ) (es : List (List Bool × List Bool)) (k v : List Bool)
        (d : Cfg 5 Bool S x),
        d.state = some entry → d.workTapePos 0 = o → KeyTableAt d 0 o es → WordAt d 1 k →
        WordAt d 2 v → (∀ e ∈ es, e.2.length = v.length) → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (keyTableLength es + k.length + v.length + 1))
          (C * (keyTableLength es + k.length + v.length + 1))
          { d with state := some exit, workTapes := keyTableWrite d 0 o (keyAssign es k v) } := by
  classical
  refine ⟨kt_TableState, inferInstance, inferInstance, kt_tableTM true,
    ⟨.start, .run⟩, ⟨.done, false⟩, 64, ?_⟩
  intro x o es k v d hd hpos ht hk hv hwidth hs
  exact kt_reaches_of_run true _ d _ rfl
    (kt_assign_run_within o es k v d hd hpos ht hk hv hwidth hs)

end Turing
