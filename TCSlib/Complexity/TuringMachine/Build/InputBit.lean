/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.WordArith
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.SeamLayout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading an input bit at a position held in a word

The input of a machine is read in place: its head moves, and nothing is copied to a work tape.
This file constructs the row that reads the input bit at a position given as a signed word on a work
tape, with the input's length in binary on another: it writes the word `1` if the position lies
on the input and the bit there is `true`, and the word `0` otherwise, off the input and at
negative positions included. Its work-tape space is `O(W + log n)`, not `O(n)`, so a logarithmic
space bound survives it. It is the `rdIn` instruction of a word RAM run on a Turing machine
(`WordRAM.exists_simulation`).

## Main results

* `Turing.exists_inputBitTM`: the row, within `O(W + n)` steps and `O(W + log n)` cells of
  radius.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: the read-only input of a space-bounded machine;
  Exercise 1.9.)
-/

namespace Turing

/-! ## Private input-position arithmetic -/

/-- The remembered order after scanning two little-endian words. Missing high digits are
zero, and a higher unequal pair replaces the order remembered from the lower digits. -/
private def inputBitOrder (lower : Bool) : List Bool → List Bool → Bool
  | [], [] => lower
  | b :: u, [] => inputBitOrder (if b then false else lower) u []
  | [], b :: v => inputBitOrder (if b then true else lower) [] v
  | b :: u, c :: v => inputBitOrder (if b = c then lower else c) u v
termination_by u v => u.length + v.length

/-- The remembered comparison equals the order of the words' values; the incoming comparison
breaks ties. This includes unequal word lengths and high zero padding.

**Proof sketch.** Induct over the two lists together. `Nat.ofDigits_cons` exposes each low
bit, and the order of the remaining high bits decides unless their values agree. In that
case the low bits, then the incoming remembered order, decide. -/
private theorem inputBitOrder_spec (lower : Bool) (u v : List Bool) :
    inputBitOrder lower u v = true ↔
      Nat.ofDigits (2 : ℕ) (u.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (v.map Bool.toNat) ∨
        (Nat.ofDigits (2 : ℕ) (u.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (v.map Bool.toNat) ∧
          lower = true) := by
  induction lower, u, v using inputBitOrder.induct with
  | case1 lower => simp only [inputBitOrder, List.map_nil, Nat.ofDigits_nil]; simp
  | case2 lower b u ih =>
    simp only [dite_eq_ite] at ih
    rw [inputBitOrder, ih]
    clear ih
    cases b <;> cases lower <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.map_cons, List.map_nil,
        Bool.toNat_false, Bool.toNat_true, Nat.ofDigits_cons, Nat.ofDigits_nil] <;> simp
  | case3 lower b v ih =>
    simp only [dite_eq_ite] at ih
    rw [inputBitOrder, ih]
    clear ih
    cases b <;> cases lower <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.map_cons, List.map_nil,
        Bool.toNat_false, Bool.toNat_true, Nat.ofDigits_cons, Nat.ofDigits_nil] <;> simp <;> omega
  | case4 lower b u c v ih =>
    simp only [dite_eq_ite] at ih
    rw [inputBitOrder, ih]
    clear ih
    cases b <;> cases c <;> cases lower <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, List.map_cons,
        Bool.toNat_false, Bool.toNat_true, Nat.ofDigits_cons] <;> simp <;> omega

/-- Starting with equality compares the unsigned values of any two bit lists. -/
private theorem inputBitOrder_lt (u v : List Bool) :
    inputBitOrder false u v = true ↔
      Nat.ofDigits (2 : ℕ) (u.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (v.map Bool.toNat) := by
  rw [inputBitOrder_spec]
  simp only [Bool.false_eq_true, and_false, or_false]

/-- A higher unequal digit pair decides the order of two little-endian prefixes. -/
private def inputBitNext (lower b c : Bool) : Bool := if b = c then lower else c

/-- The remembered order after `r` synchronized input-word positions. -/
private def inputBitPrefix (lower : Bool) (u v : List Bool) : ℕ → Bool
  | 0 => lower
  | r + 1 => inputBitNext (inputBitPrefix lower u v r) (u.getD r false) (v.getD r false)

/-- Processing the first digit pair first shifts the rest of the prefix scan to the tails. -/
private theorem inputBitPrefix_shift (lower : Bool) (u v : List Bool) (r : ℕ) :
    inputBitPrefix lower u v (r + 1) =
      inputBitPrefix (inputBitNext lower (u.getD 0 false) (v.getD 0 false)) u.tail v.tail r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [inputBitPrefix, ih, inputBitPrefix]
    cases u <;> cases v <;>
      simp only [List.tail_nil, List.tail_cons, List.getD_nil, List.getD_cons_succ]

/-- Scanning through the longer word computes the full unsigned comparison. -/
private theorem inputBitPrefix_complete (lower : Bool) (u v : List Bool) :
    inputBitPrefix lower u v (max u.length v.length) = inputBitOrder lower u v := by
  induction lower, u, v using inputBitOrder.induct with
  | case1 lower => simp only [List.length_nil, Nat.zero_max, inputBitPrefix, inputBitOrder]
  | case2 lower b u ih =>
    rw [show max (b :: u).length ([] : List Bool).length = u.length + 1 by simp,
      inputBitPrefix_shift, inputBitOrder]
    cases b <;> simpa [inputBitNext, dite_eq_ite] using ih
  | case3 lower b v ih =>
    rw [show max ([] : List Bool).length (b :: v).length = v.length + 1 by simp,
      inputBitPrefix_shift, inputBitOrder]
    cases b <;> simpa [inputBitNext, dite_eq_ite] using ih
  | case4 lower b u c v ih =>
    rw [show max (b :: u).length (c :: v).length = max u.length v.length + 1 by
      simp only [List.length_cons]; omega, inputBitPrefix_shift, inputBitOrder]
    simpa [inputBitNext, dite_eq_ite] using ih

/-! ## Private comparison row -/

/-- The comparison sweep carries the remembered order and then returns it at an exit. -/
private inductive InputBitComparePhase where
  | scan (lt : Bool)
  | done (lt : Bool)
deriving DecidableEq, Fintype

/-- A read-only comparison pass over tapes zero and one. The catalog's `compareTM` tests
equality and stops at its first differing cell; no row compares unequal-width numeric words.
This pass remembers the highest unequal bit pair, parking a head at its right delimiter
while the other word continues. Its exit advances both heads one cell beyond the delimiters,
so the published `skipBackTM` can restore each head. -/
private def inputBitCompareForward : MultiTapeTM 5 Bool InputBitComparePhase where
  q₀ := .scan false
  tr := fun q _ work => match q with
    | .scan lower =>
      if work 0 = none ∧ work 1 = none then
        ⟨0, fun j => (none, if j = 0 ∨ j = 1 then .pos else 0), none, some (.done lower)⟩
      else
        ⟨0, fun j => (none, if j = 0 then (if (work 0).isSome then .pos else 0)
          else if j = 1 then (if (work 1).isSome then .pos else 0) else 0),
          none, some (.scan (inputBitNext lower ((work 0).getD false) ((work 1).getD false)))⟩
    | .done lt => inputMoveAction 0 (.done lt)

/-- The forward sweep at index `r`: each head stops advancing at its word's delimiter. -/
private def inputBitCompareCfg {x : List Bool} (d : Cfg 5 Bool InputBitComparePhase x)
    (u v : List Bool) (r : ℕ) : Cfg 5 Bool InputBitComparePhase x :=
  { d with
    state := some (.scan (inputBitPrefix false u v r))
    workTapePos := fun j => d.workTapePos j +
      if j = 0 then ((min r u.length : ℕ) : ℤ)
      else if j = 1 then ((min r v.length : ℕ) : ℤ) else 0 }

/-- The forward comparison's exit, one cell beyond each right delimiter. -/
private def inputBitCompareDone {x : List Bool} (d : Cfg 5 Bool InputBitComparePhase x)
    (u v : List Bool) : Cfg 5 Bool InputBitComparePhase x :=
  { d with
    state := some (.done (inputBitOrder false u v))
    workTapePos := fun j => d.workTapePos j +
      if j = 0 then ((u.length + 1 : ℕ) : ℤ)
      else if j = 1 then ((v.length + 1 : ℕ) : ℤ) else 0 }

/-- A nonwriting action with an arbitrary work-head displacement vector preserves all data.
The published one-tape action lemmas do not cover the comparison's two moving heads. -/
private theorem inputBit_move_step {S : Type} {x : List Bool} (M : MultiTapeTM 5 Bool S)
    (d : Cfg 5 Bool S x) (q q' : S) (moves : Fin 5 → SignType) (hq : d.state = some q)
    (htr : M.tr q d.inputSymbol d.workTapeSymbols =
      ⟨0, fun j => (none, moves j), none, some q'⟩) :
    M.step d = { d with state := some q', workTapePos := fun j => d.workTapePos j + moves j } := by
  rw [MultiTapeTM.step_of_some hq, htr]
  apply Cfg.ext
  · rw [Action.apply_state]
  · rw [Action.apply_inputPos, moveInputPos_zero]
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    simp only [Option.getD_none, Function.update_eq_self]
  · funext j
    rw [Action.apply_workTapePos]
  · rw [Action.apply_output]
    simp only [Option.toList_none, List.append_nil]

/-- The two parked-or-advancing heads read the corresponding optional digits.

**Proof sketch.** Read a cell through `wordAt_iff` and `FinTM.bufferTape_nat`. The parked
index is the minimum of the scan index and the word length. Past that length both the
parked delimiter and the optional list lookup are blank. -/
private theorem inputBitCompareCfg_reads {x : List Bool}
    (d : Cfg 5 Bool InputBitComparePhase x) (u v : List Bool) (r : ℕ)
    (hu : WordAt d 0 u) (hv : WordAt d 1 v) :
    (inputBitCompareCfg d u v r).workTapeSymbols 0 = u[r]? ∧
      (inputBitCompareCfg d u v r).workTapeSymbols 1 = v[r]? := by
  have read (j : Fin 5) (w : List Bool) (hw : WordAt d j w)
      (hp : (inputBitCompareCfg d u v r).workTapePos j =
        d.workTapePos j + ((min r w.length : ℕ) : ℤ)) :
      (inputBitCompareCfg d u v r).workTapeSymbols j = w[r]? := by
    rw [Cfg.workTapeSymbols_eq]
    change d.workTapes j ((inputBitCompareCfg d u v r).workTapePos j) = _
    rw [hp, (wordAt_iff d j w).mp hw _ (by omega) (by omega), FinTM.bufferTape_nat]
    by_cases hr : r ≤ w.length
    · rw [Nat.min_eq_left hr]
    · rw [Nat.min_eq_right (by omega), List.getElem?_eq_none (Nat.le_refl w.length),
        List.getElem?_eq_none (by omega)]
  exact ⟨read 0 u hu (by simp [inputBitCompareCfg]),
    read 1 v hv (by simp [inputBitCompareCfg])⟩

/-- One forward comparison step advances each unfinished word head and updates the order.

**Proof sketch.** `inputBitCompareCfg_reads` identifies the scanned symbols. Before the
longer word ends, they cannot both be blank. The transition is a nonwriting two-head move
(`inputBit_move_step`), and each head's increment is the difference between its two
successive minimum indices. The control update is `inputBitPrefix`'s successor equation. -/
private theorem inputBitCompareForward_step {x : List Bool}
    (d : Cfg 5 Bool InputBitComparePhase x) (u v : List Bool)
    (hu : WordAt d 0 u) (hv : WordAt d 1 v) (r : ℕ) (hr : r < max u.length v.length) :
    inputBitCompareForward.step (inputBitCompareCfg d u v r) =
      inputBitCompareCfg d u v (r + 1) := by
  obtain ⟨hread₀, hread₁⟩ := inputBitCompareCfg_reads d u v r hu hv
  have hstop : ¬ (u[r]? = none ∧ v[r]? = none) := by
    intro h
    rcases lt_max_iff.mp hr with hlt | hlt
    · rw [List.getElem?_eq_getElem hlt] at h
      cases h.1
    · rw [List.getElem?_eq_getElem hlt] at h
      cases h.2
  let moves : Fin 5 → SignType := fun j =>
    if j = 0 then (if (u[r]?).isSome then .pos else 0)
    else if j = 1 then (if (v[r]?).isSome then .pos else 0) else 0
  have htr : inputBitCompareForward.tr (.scan (inputBitPrefix false u v r))
      (inputBitCompareCfg d u v r).inputSymbol (inputBitCompareCfg d u v r).workTapeSymbols =
      ⟨0, fun j => (none, moves j), none, some (.scan (inputBitPrefix false u v (r + 1)))⟩ := by
    simp only [inputBitCompareForward, hread₀, hread₁, if_neg hstop,
      inputBitPrefix, List.getD_eq_getElem?_getD, moves]
  have hstep := inputBit_move_step inputBitCompareForward (inputBitCompareCfg d u v r)
    (.scan (inputBitPrefix false u v r)) (.scan (inputBitPrefix false u v (r + 1)))
    moves rfl htr
  have delta (w : List Bool) :
      ((min r w.length : ℕ) : ℤ) +
        ((if (w[r]?).isSome then .pos else 0 : SignType) : ℤ) =
          ((min (r + 1) w.length : ℕ) : ℤ) := by
    by_cases h : r < w.length
    · simp only [List.getElem?_eq_getElem h, Option.isSome_some, if_true,
        SignType.pos_eq_one, SignType.coe_one]
      omega
    · simp only [List.getElem?_eq_none (by omega : w.length ≤ r), Option.isSome_none,
        Bool.false_eq_true, if_false, SignType.coe_zero, add_zero]
      omega
  rw [hstep]
  apply Cfg.ext <;> try rfl
  funext j
  by_cases h₀ : j = 0
  · subst j
    simp only [inputBitCompareCfg, moves, if_pos rfl, if_true]
    linarith [delta u]
  · by_cases h₁ : j = 1
    · subst j
      simp only [inputBitCompareCfg, moves, if_neg h₀, if_true]
      linarith [delta v]
    · simp only [inputBitCompareCfg, moves, if_neg h₀, if_neg h₁,
        SignType.coe_zero, add_zero]

/-- At both delimiters the comparison exits with the complete remembered order.

**Proof sketch.** Both symbols in `inputBitCompareCfg_reads` are blank at the maximum
length. The exit action advances the two heads once; `inputBitPrefix_complete` identifies
the returned order, and the parked head offsets are the two full word lengths. -/
private theorem inputBitCompareForward_turn {x : List Bool}
    (d : Cfg 5 Bool InputBitComparePhase x) (u v : List Bool)
    (hu : WordAt d 0 u) (hv : WordAt d 1 v) :
    inputBitCompareForward.step (inputBitCompareCfg d u v (max u.length v.length)) =
      inputBitCompareDone d u v := by
  obtain ⟨hread₀, hread₁⟩ := inputBitCompareCfg_reads d u v (max u.length v.length) hu hv
  rw [List.getElem?_eq_none (le_max_left _ _)] at hread₀
  rw [List.getElem?_eq_none (le_max_right _ _)] at hread₁
  let moves : Fin 5 → SignType := fun j => if j = 0 ∨ j = 1 then .pos else 0
  have htr : inputBitCompareForward.tr
      (.scan (inputBitPrefix false u v (max u.length v.length)))
      (inputBitCompareCfg d u v (max u.length v.length)).inputSymbol
      (inputBitCompareCfg d u v (max u.length v.length)).workTapeSymbols =
        ⟨0, fun j => (none, moves j), none, some (.done (inputBitOrder false u v))⟩ := by
    simp [inputBitCompareForward, hread₀, hread₁, inputBitPrefix_complete, moves]
  have hstep := inputBit_move_step inputBitCompareForward
    (inputBitCompareCfg d u v (max u.length v.length))
    (.scan (inputBitPrefix false u v (max u.length v.length)))
    (.done (inputBitOrder false u v)) moves rfl htr
  rw [hstep]
  apply Cfg.ext <;> try rfl
  funext j
  by_cases h₀ : j = 0
  · subst j
    simp [inputBitCompareCfg, inputBitCompareDone, moves, add_assoc]
  · by_cases h₁ : j = 1
    · subst j
      simp [inputBitCompareCfg, inputBitCompareDone, moves, h₀, add_assoc]
    · simp [inputBitCompareCfg, inputBitCompareDone, moves, h₀, h₁]

/-- The forward comparison has a first exit after the longer word's length plus one step.

**Proof sketch.** Specialize `catalog_trace_run` to the forward configurations and the
stationary exit. The step and exit obligations are `inputBitCompareForward_step` and
`inputBitCompareForward_turn`. Reading `catalogTrace_eq` gives the first-exit cut and
the head envelope directly: every forward head is at its minimum index, and each exit
head is one cell beyond its word. -/
private theorem inputBitCompareForward_reaches {x : List Bool}
    (d : Cfg 5 Bool InputBitComparePhase x) (u v : List Bool)
    (hd : d.state = some (.scan false)) (hu : WordAt d 0 u) (hv : WordAt d 1 v) :
    ReachesWithin inputBitCompareForward d {some (.done false), some (.done true)}
      (max u.length v.length + 1) (max u.length v.length + 1)
      (inputBitCompareDone d u v) := by
  let L := max u.length v.length
  let F := inputBitCompareCfg d u v
  let D := inputBitCompareDone d u v
  have hstart : F 0 = d := by
    apply Cfg.ext <;> simp [F, inputBitCompareCfg, inputBitPrefix, hd]
  have hfixed : inputBitCompareForward.step D = D := by
    rw [step_of_inputMoveAction inputBitCompareForward D 0 rfl (by rfl), moveInputPos_zero]
    rfl
  have trace (t : ℕ) : inputBitCompareForward.runFrom d t = if t ≤ L then F t else D := by
    have h := catalog_trace_run inputBitCompareForward F (fun _ => D) D L
      (inputBitCompareForward_step d u v hu hv)
      (inputBitCompareForward_turn d u v hu hv)
      (fun _ _ => hfixed) hfixed hfixed t
    rw [hstart] at h
    simpa only [catalogTrace_eq, ite_self] using h
  rw [reachesWithin_iff]
  refine ⟨L + 1, le_rfl, ?_, ?_, ?_⟩
  · intro t ht
    rw [trace, if_pos (by omega)]
    simp [F, inputBitCompareCfg]
  · intro t ht j
    rw [trace]
    split_ifs with hle
    · simp only [F, inputBitCompareCfg, add_sub_cancel_left]
      split_ifs <;> rw [abs_of_nonneg (by positivity)] <;> omega
    · simp only [D, inputBitCompareDone, add_sub_cancel_left]
      split_ifs <;> rw [abs_of_nonneg (by positivity)] <;> omega
  · rw [trace, if_neg (by omega)]

/-- Reindex a contract while retaining an additional invariant in its precondition. -/
private def inputBitContractOn {S ι κ : Type} {x : List Bool} {M : MultiTapeTM 5 Bool S}
    {entry : S} {X : Set (Option S)} (C : Contract M entry X ι x) (index : κ → ι)
    (P : κ → Cfg 5 Bool S x → Prop) : Contract M entry X κ x where
  pre i d := C.pre (index i) d ∧ P i d
  time i d := C.time (index i) d
  post i d := C.post (index i) d
  lo i d := C.lo (index i) d
  hi i d := C.hi (index i) d
  run i d hd hp := C.run (index i) d hd hp.1
  exit_mem i d hd hp := C.exit_mem (index i) d hd hp.1
  cut i d hd hp := C.cut (index i) d hd hp.1
  env i d hd hp := C.env (index i) d hd hp.1

/-- The published pointwise state-map head reader also identifies the whole head vector. -/
private theorem inputBit_mapState_heads {S H : Type} {x : List Bool} (f : S → H)
    (d : Cfg 5 Bool S x) : (d.mapState f).workTapePos = d.workTapePos :=
  funext fun j => Cfg.mapState_workTapePos f d j

/-- The pointwise tape reader identifies the whole unchanged tape bank. -/
private theorem inputBit_mapState_tapes {S H : Type} {x : List Bool} (f : S → H)
    (d : Cfg 5 Bool S x) : (d.mapState f).workTapes = d.workTapes :=
  funext fun j => funext fun z => Cfg.mapState_workTapes f d j z

/-- The published seek endpoint reader identifies its whole updated head vector. -/
private theorem inputBit_seekPost_heads {S : Type} {x : List Bool} (q : S) (i : Fin 5)
    (z : ℤ) (d : Cfg 5 Bool S x) :
    (seekPost q i z d).workTapePos = Function.update d.workTapePos i z :=
  funext fun j => seekPost_workTapePos q i z d j

/-- The two published backward skips restore the two comparison heads in sequence. -/
private def inputBitCompareBack : MultiTapeTM 5 Bool (SeekPhase ⊕ SeekPhase) :=
  seamCompTM (skipBackTM 5 0) .done (skipBackTM 5 1) .run

/-- The restoration contract retains both word premises and uses the catalog rows.

**Proof sketch.** Strengthen the first skip's contract with the second word's premise using
`inputBitContractOn`, then compose the two contracts with `Contract.seq`. The first skip
changes only head zero (`skipBackTM_contract_post`, `seekPost_workTapePos`), so the second
word's premise survives the dispatch unchanged. -/
private noncomputable def inputBitCompareBackContract (x : List Bool) :
    Contract inputBitCompareBack (Sum.inl .run)
      (Option.map Sum.inr '' {some SeekPhase.done}) (List Bool × List Bool) x := by
  let first := inputBitContractOn (skipBackTM_contract (0 : Fin 5) x) Prod.fst
    (fun p d => (skipBackTM_contract (1 : Fin 5) x).pre p.2 d)
  exact Contract.seq first (skipBackTM_contract (1 : Fin 5) x) Prod.snd (by
    intro p d hd hp
    change (skipBackTM_contract (0 : Fin 5) x).pre p.1 d ∧
      (skipBackTM_contract (1 : Fin 5) x).pre p.2 d at hp
    change (skipBackTM_contract (1 : Fin 5) x).pre p.2
      (((skipBackTM_contract (0 : Fin 5) x).post p.1 d).mapState fun _ => SeekPhase.run)
    rw [skipBackTM_contract_pre]
    simp only [skipBackTM_contract_pre] at hp
    intro z hlo hhi
    simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, skipBackTM_contract_post,
      seekPost_workTapes, seekPost_workTapePos, Function.update_of_ne (by decide : (1 : Fin 5) ≠ 0)]
      using hp.2 z hlo hhi)

/-- The backward composite requires the two words immediately before their parked heads. -/
private theorem inputBitCompareBack_pre (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool (SeekPhase ⊕ SeekPhase) x) :
    (inputBitCompareBackContract x).pre p d ↔
      (∀ z : ℤ, -1 ≤ z → z ≤ (p.1.length : ℤ) →
        d.workTapes 0 (d.workTapePos 0 - p.1.length - 1 + z) = FinTM.bufferTape p.1 z) ∧
      (∀ z : ℤ, -1 ≤ z → z ≤ (p.2.length : ℤ) →
        d.workTapes 1 (d.workTapePos 1 - p.2.length - 1 + z) = FinTM.bufferTape p.2 z) := by
  simp only [inputBitCompareBackContract, Contract.seq_pre, inputBitContractOn,
    skipBackTM_contract_pre, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- The two backward skips preserve all data and subtract each word length plus one.

**Proof sketch.** Read the endpoint of `Contract.seq` and the two
`skipBackTM_contract_post` equations. The intervening state maps preserve all physical
fields, and `seekPost` changes only the indicated head. Head one is unaffected by the
first head update, so both subtractions use their original positions. -/
private theorem inputBitCompareBack_post (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool (SeekPhase ⊕ SeekPhase) x) :
    (inputBitCompareBackContract x).post p d =
      { d with
        state := some (Sum.inr SeekPhase.done)
        workTapePos := Function.update
          (Function.update d.workTapePos 0 (d.workTapePos 0 - p.1.length - 1))
          1 (d.workTapePos 1 - p.2.length - 1) } := by
  apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
    simp only [inputBitCompareBackContract, Contract.seq_post, inputBitContractOn,
      skipBackTM_contract_post, seekPost_state, seekPost_inputPos, seekPost_workTapes,
      seekPost_workTapePos, seekPost_output, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output, Option.map_some,
      inputBit_mapState_heads, inputBit_seekPost_heads,
      Function.update_of_ne (by decide : (1 : Fin 5) ≠ 0)]

/-- The two backward skips cost the sum of the word lengths plus seven steps. -/
private theorem inputBitCompareBack_time (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool (SeekPhase ⊕ SeekPhase) x) :
    (inputBitCompareBackContract x).time p d = p.1.length + p.2.length + 7 := by
  simp only [inputBitCompareBackContract, Contract.seq_time, inputBitContractOn,
    skipBackTM_contract_time]
  omega

/-- The numeric comparison pass as a composable framed contract. -/
private noncomputable def inputBitCompareForwardContract (x : List Bool) :
    Contract inputBitCompareForward (.scan false) {some (.done false), some (.done true)}
      (List Bool × List Bool) x :=
  Contract.ofReaches
    (fun p d => WordAt d 0 p.1 ∧ WordAt d 1 p.2)
    (fun p _ => max p.1.length p.2.length + 1)
    (fun p _ => max p.1.length p.2.length + 1)
    (fun p d => inputBitCompareDone d p.1 p.2)
    (fun p d hd hp => inputBitCompareForward_reaches d p.1 p.2 hd hp.1 hp.2)
    (by
      intro p d hd hp
      simp only [inputBitCompareDone]
      cases inputBitOrder false p.1 p.2 <;> simp)

/-- The forward exit places both delimited words exactly where the backward skips expect.

**Proof sketch.** Read the backward precondition with `inputBitCompareBack_pre` and the
forward endpoint with `Contract.ofReaches_post`. The state maps preserve tape data and
heads. Subtracting each word's length plus one from its forward exit position recovers
the original word origin, where `wordAt_iff` supplies the premise. -/
private theorem inputBitCompare_link (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool InputBitComparePhase x)
    (hp : (inputBitCompareForwardContract x).pre p d) :
    (inputBitCompareBackContract x).pre p
      (((inputBitCompareForwardContract x).post p d).mapState fun _ =>
        (Sum.inl SeekPhase.run : SeekPhase ⊕ SeekPhase)) := by
  simp only [inputBitCompareForwardContract, Contract.ofReaches_pre] at hp
  rw [inputBitCompareBack_pre]
  simp only [inputBitCompareForwardContract, Contract.ofReaches_post,
    Cfg.mapState_workTapes, Cfg.mapState_workTapePos, inputBitCompareDone]
  constructor
  · intro z hlo hhi
    have h := (wordAt_iff d 0 p.1).mp hp.1 z hlo hhi
    convert h using 1
    congr 1
    simp
    omega
  · intro z hlo hhi
    have h := (wordAt_iff d 1 p.2).mp hp.2 z hlo hhi
    convert h using 1
    congr 1
    simp
    omega

/-- The comparison control consists of its forward pass and the two tagged restorations. -/
private abbrev InputBitCompareState :=
  (InputBitComparePhase ⊕ (SeekPhase ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ SeekPhase)

/-- The comparison first branches on its remembered order, then restores both heads. -/
private def inputBitCompareTM : MultiTapeTM 5 Bool InputBitCompareState :=
  seamCompTM₂ inputBitCompareForward (.done false) (.done true)
    inputBitCompareBack (Sum.inl .run) inputBitCompareBack (Sum.inl .run)

/-- The comparison entry is the false-initialized forward scan. -/
private def inputBitCompareEntry : InputBitCompareState := Sum.inl (Sum.inl (.scan false))

/-- The tagged backward exit retains the comparison result in finite control. -/
private def inputBitCompareExit (lt : Bool) : InputBitCompareState :=
  if lt then Sum.inr (Sum.inr .done) else Sum.inl (Sum.inr (Sum.inr .done))

/-- The exit set supplied by the branch contract, before simplifying the two images. -/
private def inputBitCompareExits : Set (Option InputBitCompareState) :=
  (Option.map (Sum.inl ∘ Sum.inr) '' (Option.map Sum.inr '' {some SeekPhase.done})) ∪
    (Option.map Sum.inr '' (Option.map Sum.inr '' {some SeekPhase.done}))

/-- The complete comparison contract composes one forward pass with a tagged restoration. -/
private noncomputable def inputBitCompareContract (x : List Bool) :
    Contract inputBitCompareTM inputBitCompareEntry inputBitCompareExits
      (List Bool × List Bool) x :=
  Contract.branch (by decide : InputBitComparePhase.done false ≠ .done true)
    (inputBitCompareForwardContract x) (inputBitCompareBackContract x)
    (inputBitCompareBackContract x) (fun p => p) (fun p => p)
    (fun p d _ hp _ => inputBitCompare_link x p d hp)
    (fun p d _ hp _ => inputBitCompare_link x p d hp)

/-- The complete comparison has exactly the original two-word precondition. -/
private theorem inputBitCompare_pre (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool InputBitCompareState x) :
    (inputBitCompareContract x).pre p d ↔ WordAt d 0 p.1 ∧ WordAt d 1 p.2 := by
  simp only [inputBitCompareContract, Contract.branch_pre, inputBitCompareForwardContract,
    Contract.ofReaches_pre, wordAt_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- The chosen running time of the forward contract is at most its stated linear bound. -/
private theorem inputBitCompareForward_time_le (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool InputBitComparePhase x) (hd : d.state = some (.scan false))
    (hp : (inputBitCompareForwardContract x).pre p d) :
    (inputBitCompareForwardContract x).time p d ≤ max p.1.length p.2.length + 1 := by
  have hp' : WordAt d 0 p.1 ∧ WordAt d 1 p.2 := by
    simpa only [inputBitCompareForwardContract, Contract.ofReaches_pre] using hp
  unfold inputBitCompareForwardContract
  apply Contract.ofReaches_time_le <;> assumption

/-- The full comparison, including both head restorations, has linear running time.

**Proof sketch.** `Contract.branch_time` adds the forward time, one dispatch step and
`inputBitCompareBack_time`. Both continuations have the same cost. Bound the forward
time with `inputBitCompareForward_time_le` and absorb the fixed nine steps. -/
private theorem inputBitCompare_time_le (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool InputBitCompareState x) (hd : d.state = some inputBitCompareEntry)
    (hp : (inputBitCompareContract x).pre p d) :
    (inputBitCompareContract x).time p d ≤ 10 * (p.1.length + p.2.length + 1) := by
  have hd₀ : (d.mapState fun _ => InputBitComparePhase.scan false).state =
      some (.scan false) := by
    rw [Cfg.mapState_state, hd]
    rfl
  have hp₀ : (inputBitCompareForwardContract x).pre p
      (d.mapState fun _ => InputBitComparePhase.scan false) := by
    simpa only [inputBitCompareContract, Contract.branch_pre] using hp
  have ht := inputBitCompareForward_time_le x p _ hd₀ hp₀
  simp only [inputBitCompareContract, Contract.branch_time, inputBitCompareBack_time, ite_self]
  exact (Nat.add_le_add_right (Nat.add_le_add_right ht 1)
    (p.1.length + p.2.length + 7)).trans (by omega)

/-- The branch contract's image exits are exactly the false and true comparison anchors. -/
private theorem inputBitCompareExits_eq : inputBitCompareExits =
    {some (inputBitCompareExit false), some (inputBitCompareExit true)} := by
  ext q
  simp [inputBitCompareExits, inputBitCompareExit, or_comm]

/-- The complete comparison restores both heads and all data, retaining only its verdict.

**Proof sketch.** Substitute `inputBitCompareBack_post` at the forward endpoint. Its two
head subtractions cancel the forward advances; `Contract.ofReaches_post` and the state-map
readers identify all other fields. Then read `Contract.branch_post`: its two tagged
continuations have the same physical endpoint, and their tags are `inputBitCompareExit`. -/
private theorem inputBitCompare_post (x : List Bool) (p : List Bool × List Bool)
    (d : Cfg 5 Bool InputBitCompareState x) :
    (inputBitCompareContract x).post p d =
      { d with state := some (inputBitCompareExit (inputBitOrder false p.1 p.2)) } := by
  let start := d.mapState fun _ => InputBitComparePhase.scan false
  let backStart := ((inputBitCompareForwardContract x).post p start).mapState fun _ =>
    (Sum.inl SeekPhase.run : SeekPhase ⊕ SeekPhase)
  have restore : (inputBitCompareBackContract x).post p backStart =
      (⟨some (Sum.inr SeekPhase.done), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
        Cfg 5 Bool (SeekPhase ⊕ SeekPhase) x) := by
    rw [inputBitCompareBack_post]
    apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
      simp only [backStart, start, inputBitCompareForwardContract, Contract.ofReaches_post,
        inputBitCompareDone, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
        inputBit_mapState_heads]
    by_cases h₀ : j = 0
    · subst j
      simp
      omega
    · by_cases h₁ : j = 1
      · subst j
        simp [h₀]
        omega
      · simp [h₀, h₁]
  dsimp only [backStart, start] at restore
  simp only [inputBitCompareContract, Contract.branch_post]
  rw [restore]
  simp only [inputBitCompareForwardContract, Contract.ofReaches_post, inputBitCompareDone]
  rcases Bool.eq_false_or_eq_true (inputBitOrder false p.1 p.2) with horder | horder <;>
    apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
    simp [horder, inputBitCompareExit, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output]

/-- Comparing two unequal-width words preserves every physical field and returns their
unsigned order in linear time and radius.

**Proof sketch.** Use the composed contract, its exact precondition and restored endpoint.
`inputBitCompare_time_le` bounds the chosen time; `Contract.time_envelope` supplies a
sufficient linear head radius. The contract's cut is read through `inputBitCompareExits_eq`.
`inputBitOrder_lt` identifies the returned Boolean with the strict order of the values. -/
private theorem inputBitCompare_reaches {x : List Bool}
    (d : Cfg 5 Bool InputBitCompareState x) (u v : List Bool)
    (hd : d.state = some inputBitCompareEntry) (hu : WordAt d 0 u) (hv : WordAt d 1 v) :
    ReachesWithin inputBitCompareTM d
      {some (inputBitCompareExit false), some (inputBitCompareExit true)}
      (10 * (u.length + v.length + 1)) (10 * (u.length + v.length + 1))
      { d with state := some (inputBitCompareExit (inputBitOrder false u v)) } := by
  let C := inputBitCompareContract x
  have hp : C.pre (u, v) d := (inputBitCompare_pre x (u, v) d).mpr ⟨hu, hv⟩
  have ht : C.time (u, v) d ≤ 10 * (u.length + v.length + 1) :=
    inputBitCompare_time_le x (u, v) d hd hp
  rw [reachesWithin_iff]
  refine ⟨C.time (u, v) d, ht, ?_, ?_, ?_⟩
  · intro t hlt
    simpa only [inputBitCompareExits_eq] using C.cut (u, v) d hd hp t hlt
  · intro t hle j
    have h := C.time_envelope (u, v) d t hle j
    rw [Finset.mem_Icc] at h
    have hb : ((C.time (u, v) d : ℕ) : ℤ) ≤
        ((10 * (u.length + v.length + 1) : ℕ) : ℤ) := by exact_mod_cast ht
    rw [abs_le]
    constructor <;> omega
  · exact (C.run (u, v) d hd hp).trans (inputBitCompare_post x (u, v) d)

/-! ## Private word-value facts -/

/-- Adding a most-significant bit appends it to the little-endian tape word. -/
private theorem inputBit_bvBits_cons {W : ℕ} (b : Bool) (u : BitVec W) :
    bvBits (BitVec.cons b u) = bvBits u ++ [b] := by
  rw [bvBits_def, List.ofFn_succ', List.concat_eq_append, bvBits_def]
  refine congrArg₂ List.append ?_ ?_
  · apply congrArg List.ofFn
    funext i
    change (BitVec.cons b u).getLsbD i.val = u.getLsbD i.val
    rw [BitVec.getLsbD_cons, if_neg (Nat.ne_of_lt i.isLt)]
  · change [(BitVec.cons b u).getLsbD W] = [b]
    rw [BitVec.getLsbD_cons, if_pos rfl]

/-- The unsigned value of a word's tape bits is its `BitVec.toNat` value.

**Proof sketch.** Induct on the width. The zero-width case uses `bvBits_length` and
`BitVec.toNat_zero_length`. At positive width, split off the most-significant bit with
`BitVec.cons_msb_setWidth`, apply `inputBit_bvBits_cons`, and read concatenation with
`Nat.ofDigits_append`. The induction hypothesis and `BitVec.toNat_cons'` give the value. -/
private theorem inputBit_bvBits_value {W : ℕ} (u : BitVec W) :
    Nat.ofDigits 2 ((bvBits u).map Bool.toNat) = u.toNat := by
  induction W with
  | zero =>
    have hnil : bvBits u = [] := List.eq_nil_of_length_eq_zero (bvBits_length u)
    rw [hnil, List.map_nil, Nat.ofDigits_nil, BitVec.toNat_zero_length]
  | succ W ih =>
    have hcons := inputBit_bvBits_cons u.msb (u.setWidth W)
    rw [BitVec.cons_msb_setWidth] at hcons
    rw [hcons, List.map_append, Nat.ofDigits_append, List.length_map, bvBits_length]
    simp only [List.map_cons, List.map_nil, Nat.ofDigits_singleton]
    rw [ih]
    have hn := congrArg (fun v : BitVec (W + 1) => v.toNat) (BitVec.cons_msb_setWidth u)
    change (BitVec.cons u.msb (u.setWidth W)).toNat = u.toNat at hn
    rw [BitVec.toNat_cons', Nat.shiftLeft_eq] at hn
    simpa only [Nat.mul_comm, Nat.add_comm] using hn

/-- The native seek's framed conclusion is a `ReachesWithin` row. The input position in the
endpoint is the unique position with value `p`, and all work-tape contents are restored. -/
private theorem inputBit_seek_row {S : Type} (R : MultiTapeTM 2 Bool S) (entry exit : S) (C : ℕ)
    (hR : ∀ {x : List Bool} (p : ℕ) (w : List Bool),
      Nat.ofDigits (2 : ℕ) (w.map Bool.toNat) = p → p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x,
      d.state = some entry → WordAt d 0 w → (∀ q, d.workTapes 1 q = none) →
      ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
        (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
        (∀ u ≤ t, ∀ j : Fin 2,
          |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((C * (w.length + 1) : ℕ) : ℤ)) ∧
        (R.runFrom d t).state = some exit ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
        (R.runFrom d t).workTapes = d.workTapes ∧
        (R.runFrom d t).workTapePos = d.workTapePos ∧ (R.runFrom d t).output = d.output)
    {x : List Bool} (p : ℕ) (w : List Bool)
    (hp : Nat.ofDigits (2 : ℕ) (w.map Bool.toNat) = p) (hpx : p ≤ x.length + 1)
    (d : Cfg 2 Bool S x) (hd : d.state = some entry) (hw : WordAt d 0 w)
    (hb : ∀ q, d.workTapes 1 q = none) :
    ReachesWithin R d {some exit} (C * (w.length + d.inputPos.val + p + 1))
      (C * (w.length + 1))
      { d with state := some exit, inputPos := ⟨p, by omega⟩ } := by
  obtain ⟨t, ht, hcut, henv, hs, hi, hw', hh, ho⟩ := hR p w hp hpx d hd hw hb
  rw [reachesWithin_iff]
  refine ⟨t, ht, ?_, henv, ?_⟩
  · intro s hst
    simpa only [Set.mem_singleton_iff] using hcut s hst
  · apply Cfg.ext
    · exact hs
    · exact Fin.ext hi
    · exact hw'
    · exact hh
    · exact ho

/-- A nonoverflowing bit list has a successor of exactly the same width. -/
private theorem inputBit_increment_exists (w : List Bool)
    (hw : w ≠ List.replicate w.length true) :
    ∃ v, incFixed w = some v ∧ v.length = w.length := by
  have hn : incFixed w ≠ none := fun h => hw ((incFixed_eq_none_iff_replicate w).mp h)
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hn
  exact ⟨v, hv, incFixed_length hv⟩

/-- A successful fixed-width increment adds one to the unsigned value of the bits.

**Proof sketch.** Induct on the source list using the published equations
`incFixed_nil`, `incFixed_false_cons` and `incFixed_true_cons`. A low zero absorbs
the carry. For a low one, split on the tail's increment: overflow contradicts
success, and success reduces the value equation to the induction hypothesis
with both tail values doubled. -/
private theorem inputBit_increment_value (w v : List Bool) (h : incFixed w = some v) :
    Nat.ofDigits 2 (v.map Bool.toNat) = Nat.ofDigits 2 (w.map Bool.toNat) + 1 := by
  induction w generalizing v with
  | nil =>
    rw [incFixed_nil] at h
    cases h
  | cons bit w ih =>
    cases bit with
    | false =>
      rw [incFixed_false_cons, Option.some.injEq] at h
      subst v
      simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_false, Bool.toNat_true]
      omega
    | true =>
      rw [incFixed_true_cons] at h
      cases ht : incFixed w with
      | none =>
        simp only [ht, Option.map_none] at h
        cases h
      | some tail =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst v
        have htail := ih tail ht
        simp only [List.map_cons, Nat.ofDigits_cons, Bool.toNat_false, Bool.toNat_true]
        omega

/-- The fixed-width successor bits used by the input-head counter. -/
private def inputBitSuccBits {W : ℕ} (u : BitVec W) : List Bool :=
  (incFixed (bvBits u)).getD []

/-- A positive-width nonnegative signed position has a nonoverflowing successor counter.

**Proof sketch.** Nonnegativity makes the most-significant bit false, by
`BitVec.toInt_pos_iff` and `BitVec.msb_eq_false_iff_two_mul_lt`. The decomposition
`BitVec.cons_msb_setWidth`, read through `inputBit_bvBits_cons`, shows a false bit in
the tape word, so `inputBit_increment_exists` applies. Its value is
`inputBit_increment_value`, `inputBit_bvBits_value` and `BitVec.toNat_toInt_of_msb`. -/
private theorem inputBitSuccBits_spec {W : ℕ} (u : BitVec W) (hW : 0 < W)
    (hu : 0 ≤ u.toInt) :
    incFixed (bvBits u) = some (inputBitSuccBits u) ∧
      (inputBitSuccBits u).length = W ∧
      Nat.ofDigits 2 ((inputBitSuccBits u).map Bool.toNat) = u.toInt.toNat + 1 := by
  have hm : u.msb = false :=
    BitVec.msb_eq_false_iff_two_mul_lt.mpr (BitVec.toInt_pos_iff.mp hu)
  have hf : false ∈ bvBits u := by
    cases W with
    | zero => omega
    | succ n =>
      have hs := inputBit_bvBits_cons u.msb (u.setWidth n)
      rw [BitVec.cons_msb_setWidth] at hs
      rw [hs, hm]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hnot : bvBits u ≠ List.replicate (bvBits u).length true := by
    intro he
    rw [he] at hf
    simp at hf
  obtain ⟨v, hv, hlen⟩ := inputBit_increment_exists (bvBits u) hnot
  have he : inputBitSuccBits u = v := by simp only [inputBitSuccBits, hv, Option.getD_some]
  rw [he]
  refine ⟨hv, hlen.trans (bvBits_length u), ?_⟩
  rw [inputBit_increment_value _ _ hv, inputBit_bvBits_value, BitVec.toNat_toInt_of_msb u hm]

/-- A native seek witness with the endpoint and the head envelope packaged for composition.
Its position word is restored, its scratch tape remains blank, and the input head lands at `p`.

**Proof sketch.** Choose the machine from `exists_inputSeekTM`, read its delimited-word premise
with `wordAt_iff`, and apply `inputBit_seek_row` to assemble its fieldwise endpoint. -/
private theorem inputBit_exists_seek_row :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 2 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} (p : ℕ) (w : List Bool)
        (hp : Nat.ofDigits (2 : ℕ) (w.map Bool.toNat) = p) (hpx : p ≤ x.length + 1)
        (d : Cfg 2 Bool S x), d.state = some entry → WordAt d 0 w →
        (∀ q, d.workTapes 1 q = none) →
        ReachesWithin R d {some exit} (C * (w.length + d.inputPos.val + p + 1))
          (C * (w.length + 1))
          { d with state := some exit, inputPos := ⟨p, by omega⟩ } := by
  obtain ⟨S, hS, hD, R, entry, exit, C, hR⟩ := exists_inputSeekTM
  refine ⟨S, hS, hD, R, entry, exit, C, ?_⟩
  intro x p w hp hpx d hd hw hb
  apply inputBit_seek_row R entry exit C ?_ p w hp hpx d hd hw hb
  intro y q v hq hqy c hc hv hblank
  exact hR q v hq hqy c hc ((wordAt_iff c 0 v).mp hv) hblank

/-! ## Private composition adapters -/

/-- The physical fields of a reader configuration, independent of its control states. -/
private structure InputBitData (x : List Bool) where
  inputPos : Fin (x.length + 2)
  workTapes : Fin 5 → ℤ → Option Bool
  workTapePos : Fin 5 → ℤ
  output : List Bool

/-- Attach a live control state to physical fields. -/
private def InputBitData.cfg {x : List Bool} (d : InputBitData x) {S : Type} (s : S) :
    Cfg 5 Bool S x := ⟨some s, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-- Forget a configuration's control state. -/
private def InputBitData.ofCfg {x : List Bool} {S : Type} (d : Cfg 5 Bool S x) :
    InputBitData x := ⟨d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-- Forgetting an attached state recovers the physical fields. -/
private theorem InputBitData.ofCfg_cfg {x : List Bool} {S : Type} (d : InputBitData x) (s : S) :
    InputBitData.ofCfg (d.cfg s) = d := rfl

/-- Reattaching a configuration's live state recovers it. -/
private theorem InputBitData.cfg_ofCfg {x : List Bool} {S : Type} (d : Cfg 5 Bool S x) (s : S)
    (hd : d.state = some s) : (InputBitData.ofCfg d).cfg s = d := by
  exact Cfg.ext hd.symm rfl rfl rfl rfl

/-- Re-tagging a live configuration only changes its attached state. -/
private theorem InputBitData.cfg_mapState {x : List Bool} {S T : Type} (d : InputBitData x)
    (s : S) (f : S → T) : (d.cfg s).mapState f = d.cfg (f s) := by
  apply Cfg.ext <;> simp only [InputBitData.cfg, Cfg.mapState_state, Cfg.mapState_inputPos,
    inputBit_mapState_tapes, inputBit_mapState_heads, Cfg.mapState_output, Option.map_some]

/-- Forgetting control is invariant under a re-tagging. -/
private theorem InputBitData.ofCfg_mapState {x : List Bool} {S T : Type} (d : Cfg 5 Bool S x)
    (f : S → T) : InputBitData.ofCfg (d.mapState f) = InputBitData.ofCfg d := by
  simp only [InputBitData.ofCfg, Cfg.mapState_inputPos, inputBit_mapState_tapes,
    inputBit_mapState_heads, Cfg.mapState_output]

/-- A single-exit catalog composition with a state-independent physical specification.
The head-return clause lets subsequent calls use the same origins. -/
private structure InputBitCall (ι : Type)
    (P : {x : List Bool} → ι → InputBitData x → Prop)
    (F : {x : List Bool} → ι → InputBitData x → InputBitData x)
    (B E : List Bool → ι → ℕ) where
  S : Type
  finite : Fintype S
  decEq : DecidableEq S
  M : MultiTapeTM 5 Bool S
  entry : S
  exit : S
  heads : ∀ {x} i (d : InputBitData x), P i d → (F i d).workTapePos = d.workTapePos
  reaches : ∀ {x} i (d : InputBitData x), P i d →
    ReachesWithin M (d.cfg entry) {some exit} (B x i) (E x i) ((F i d).cfg exit)

/-- Package a physical call as the published `Contract.ofReaches` adapter. -/
private noncomputable def InputBitCall.contract {ι : Type}
    {P : {x : List Bool} → ι → InputBitData x → Prop}
    {F : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E : List Bool → ι → ℕ} (R : InputBitCall ι P F B E) (x : List Bool) :
    Contract R.M R.entry {some R.exit} ι x :=
  Contract.ofReaches (fun i d => P i (InputBitData.ofCfg d)) (fun i _ => B x i)
    (fun i _ => E x i) (fun i d => (F i (InputBitData.ofCfg d)).cfg R.exit)
    (fun i d hd hp => by
      have h := R.reaches i (InputBitData.ofCfg d) hp
      rw [InputBitData.cfg_ofCfg d R.entry hd] at h
      exact h)
    (fun _ _ _ _ => Set.mem_singleton _)

/-- The call's chosen contract time obeys its advertised bound. -/
private theorem InputBitCall.time_le {ι : Type}
    {P : {x : List Bool} → ι → InputBitData x → Prop}
    {F : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E : List Bool → ι → ℕ} (R : InputBitCall ι P F B E) {x : List Bool} (i : ι)
    (d : Cfg 5 Bool R.S x) (hd : d.state = some R.entry) (hp : P i (InputBitData.ofCfg d)) :
    (R.contract x).time i d ≤ B x i := by
  exact Contract.ofReaches_time_le _ _ _ _ _ _ i d hd hp

/-- Sequence two head-returning calls with the published seam host.

**Proof sketch.** Convert both calls with `InputBitCall.contract`, then apply `Contract.seq`.
Its time is bounded by the sum of the two advertised times and one dispatch. Its envelope
is the hull of the two radius intervals; the first call returns the heads, so both intervals
have the original centers. `Contract.seq_post` gives the composed physical endpoint. -/
private noncomputable def InputBitCall.seq {ι : Type}
    {P Q : {x : List Bool} → ι → InputBitData x → Prop}
    {F G : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E D H : List Bool → ι → ℕ} (R : InputBitCall ι P F B E)
    (T : InputBitCall ι Q G D H)
    (link : ∀ {x} i (d : InputBitData x), P i d → Q i (F i d)) :
    InputBitCall ι P (fun i d => G i (F i d))
      (fun x i => B x i + 1 + D x i) (fun x i => E x i + H x i) where
  S := R.S ⊕ T.S
  finite := by letI := R.finite; letI := T.finite; infer_instance
  decEq := by letI := R.decEq; letI := T.decEq; infer_instance
  M := by letI := R.decEq; exact seamCompTM R.M R.exit T.M T.entry
  entry := Sum.inl R.entry
  exit := Sum.inr T.exit
  heads i d hp := (T.heads i _ (link i d hp)).trans (R.heads i d hp)
  reaches := by
    intro x i d hp
    letI := R.decEq
    let C₁ := R.contract x
    let C₂ := T.contract x
    have hlink : ∀ i c, c.state = some R.entry → C₁.pre i c →
        C₂.pre i ((C₁.post i c).mapState fun _ => T.entry) := by
      intro a c _ hc
      simp only [C₁, C₂, InputBitCall.contract, Contract.ofReaches_pre,
        Contract.ofReaches_post, InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] at hc ⊢
      exact link a _ hc
    let C := C₁.seq C₂ id hlink
    have hc : C.pre i (d.cfg (Sum.inl R.entry)) := by
      simpa only [C, Contract.seq_pre, C₁, InputBitCall.contract, Contract.ofReaches_pre,
        InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] using hp
    have ht₁ := R.time_le i (d.cfg R.entry) rfl (by simpa only [InputBitData.ofCfg_cfg] using hp)
    have ht₂ := T.time_le i ((F i d).cfg T.entry) rfl
      (by simpa only [InputBitData.ofCfg_cfg] using link i d hp)
    have ht : C.time i (d.cfg (Sum.inl R.entry)) ≤ B x i + 1 + D x i := by
      simpa only [C, Contract.seq_time, C₁, C₂, InputBitCall.contract,
        Contract.ofReaches_post, InputBitData.cfg_mapState, InputBitData.ofCfg_cfg, id_eq]
        using Nat.add_le_add (Nat.add_le_add_right ht₁ 1) ht₂
    rw [reachesWithin_iff]
    refine ⟨C.time i _, ht, ?_, ?_, ?_⟩
    · intro s hs he
      exact C.cut i _ rfl hc s hs ⟨some T.exit, Set.mem_singleton _, he.symm⟩
    · intro s hs j
      have he := C.env i (d.cfg (Sum.inl R.entry)) rfl hc s hs j
      simp only [C, Contract.seq_lo, Contract.seq_hi, C₁, C₂, InputBitCall.contract,
        Contract.ofReaches_lo, Contract.ofReaches_hi, Contract.ofReaches_post,
        InputBitData.cfg_mapState, InputBitData.ofCfg_cfg, id_eq,
        Finset.mem_Icc] at he
      simp only [InputBitData.cfg] at he ⊢
      rw [R.heads i d hp] at he
      rw [abs_le]
      constructor <;> push_cast <;> have hE := Nat.zero_le (E x i) <;>
        have hH := Nat.zero_le (H x i) <;> omega
    · have hr := C.run i (d.cfg (Sum.inl R.entry)) rfl hc
      simpa only [C, Contract.seq_post, C₁, C₂, InputBitCall.contract,
        Contract.ofReaches_post, InputBitData.cfg_mapState, InputBitData.ofCfg_cfg, id_eq]
        using hr

/-- Strengthen a call's precondition, identify its physical endpoint and enlarge its bounds. -/
private def InputBitCall.adapt {ι : Type}
    {P Q : {x : List Bool} → ι → InputBitData x → Prop}
    {F G : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E D H : List Bool → ι → ℕ} (R : InputBitCall ι P F B E)
    (hp : ∀ {x} i (d : InputBitData x), Q i d → P i d)
    (hf : ∀ {x} i (d : InputBitData x), Q i d → F i d = G i d)
    (hb : ∀ x i, B x i ≤ D x i) (he : ∀ x i, E x i ≤ H x i) :
    InputBitCall ι Q G D H where
  S := R.S
  finite := R.finite
  decEq := R.decEq
  M := R.M
  entry := R.entry
  exit := R.exit
  heads i d h := by rw [← hf i d h]; exact R.heads i d (hp i d h)
  reaches i d h := by
    rw [← hf i d h]
    exact (R.reaches i d (hp i d h)).mono (hb _ i) (he _ i)

/-- The original machine and a terminal catalog phase used to identify live exits. -/
private def InputBitJoinPhase (S : Type) : Bool → Type
  | false => S
  | true => SeekPhase

/-- Place a source machine beside the terminal phase in the published phase host. -/
private def inputBitJoinMachines {S : Type} (M : MultiTapeTM 5 Bool S) :
    (b : Bool) → MultiTapeTM 5 Bool (InputBitJoinPhase S b)
  | false => M
  | true => skipTM 5 0

/-- Redirect exactly the live exits to one terminal anchor. -/
private noncomputable def inputBitJoinRed {S : Type} (X : Set (Option S)) :
    (b : Bool) → InputBitJoinPhase S b → Option (Σ b, InputBitJoinPhase S b) := by
  classical
  exact fun
    | false, s => if some s ∈ X then some ⟨true, SeekPhase.done⟩ else none
    | true, _ => none

/-- Identify a finite family's live exits using `Contract.inPhase`.

**Proof sketch.** The source row becomes a contract by `Contract.ofReaches`. Its live exits
are all redirected by `inputBitJoinRed` to a different, terminal phase. Apply
`Contract.inPhase`: its extra dispatch costs one step and preserves the source envelope.
The endpoint is the specified physical data with the terminal anchor attached. -/
private noncomputable def InputBitCall.close {ι S : Type} [Fintype S] [DecidableEq S]
    {P : {x : List Bool} → ι → InputBitData x → Prop}
    {F : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E : List Bool → ι → ℕ} (M : MultiTapeTM 5 Bool S) (entry : S)
    (X : Set (Option S)) (hnone : none ∉ X)
    (e : {x : List Bool} → ι → InputBitData x → S)
    (he : ∀ {x} i (d : InputBitData x), P i d → some (e i d) ∈ X)
    (hh : ∀ {x} i (d : InputBitData x), P i d → (F i d).workTapePos = d.workTapePos)
    (hr : ∀ {x} i (d : InputBitData x), P i d →
      ReachesWithin M (d.cfg entry) X (B x i) (E x i) ((F i d).cfg (e i d))) :
    InputBitCall ι P F (fun x i => B x i + 1) E := by
  classical
  let Ph := InputBitJoinPhase S
  let Mf := inputBitJoinMachines M
  let red := inputBitJoinRed X
  let q₀ : Σ b, Ph b := ⟨false, entry⟩
  let qf : Σ b, Ph b := ⟨true, SeekPhase.done⟩
  haveI : (b : Bool) → Fintype (Ph b) := by
    intro b
    cases b
    · change Fintype S; infer_instance
    · change Fintype SeekPhase; infer_instance
  refine ⟨(Σ b, Ph b), inferInstance, inferInstance, phaseHostTM Mf q₀ red,
    q₀, qf, hh, ?_⟩
  intro x i d hp
  let C₀ : Contract M entry X ι x := Contract.ofReaches
    (fun a c => P a (InputBitData.ofCfg c)) (fun a _ => B x a) (fun a _ => E x a)
    (fun a c => (F a (InputBitData.ofCfg c)).cfg (e a (InputBitData.ofCfg c)))
    (fun a c hc hP => by
      have h := hr a (InputBitData.ofCfg c) hP
      rw [InputBitData.cfg_ofCfg c entry hc] at h
      exact h)
    (fun a c _ hP => he a _ hP)
  let C := Contract.inPhase Mf q₀ red false C₀ hnone
    (fun s hs => by simp only [red, inputBitJoinRed, if_neg hs])
    (fun s hs => ⟨qf, by simp only [red, inputBitJoinRed, if_pos hs, qf], by
      change true ≠ false; decide⟩)
  have hc : C.pre i (d.cfg q₀) := by
    simpa only [C, Contract.inPhase_pre, C₀, Contract.ofReaches_pre,
      InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] using hp
  have ht₀ : C₀.time i (d.cfg entry) ≤ B x i :=
    Contract.ofReaches_time_le _ _ _ _ _ _ i _ rfl (by
      simpa only [InputBitData.ofCfg_cfg] using hp)
  rw [reachesWithin_iff]
  refine ⟨C.time i (d.cfg q₀), ?_, ?_, ?_, ?_⟩
  · simpa only [C, Contract.inPhase_time, InputBitData.cfg_mapState]
      using Nat.add_le_add_right ht₀ 1
  · intro s hs hs'
    apply C.cut i _ rfl hc s hs
    exact ⟨e i d, he i d hp, hs'.trans (by
      simp only [red, inputBitJoinRed, if_pos (he i d hp), qf])⟩
  · intro s hs j
    have h := C.env i (d.cfg q₀) rfl hc s hs j
    simp only [C, Contract.inPhase_lo, Contract.inPhase_hi, C₀, Contract.ofReaches_lo,
      Contract.ofReaches_hi, InputBitData.cfg_mapState, Finset.mem_Icc] at h
    simp only [InputBitData.cfg] at h
    rw [abs_le]
    simp only [InputBitData.cfg]
    constructor <;> omega
  · have h := C.run i (d.cfg q₀) rfl hc
    simp only [C, Contract.inPhase_post, C₀, Contract.ofReaches_post,
      InputBitData.cfg_mapState, InputBitData.ofCfg_cfg] at h
    rw [h]
    apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
      simp only [Cfg.bindState_state, Cfg.bindState_inputPos, Cfg.bindState_workTapes,
        Cfg.bindState_workTapePos, Cfg.bindState_output, InputBitData.cfg,
        Option.bind_some, red, inputBitJoinRed, if_pos (he i d hp), qf]

/-- Compose a read-only test with two calls and identify the resulting exits.

**Proof sketch.** Turn the test into `Contract.ofReaches`, use `Contract.branch` for its two
continuations, and `InputBitCall.close` for their final anchors. The test returns all physical
fields, so the branch contracts have the original head origins. Bound the selected time by
the sum of the two continuation bounds, and their envelope hull by the sum of all three radii.
The branch's endpoint equation gives the selected physical transformation. -/
private noncomputable def InputBitCall.branch {ι S : Type} [Fintype S] [DecidableEq S]
    {P Q V : {x : List Bool} → ι → InputBitData x → Prop}
    {F G : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B E D H A L : List Bool → ι → ℕ} (M : MultiTapeTM 5 Bool S)
    (entry yes no : S) (hne : yes ≠ no)
    (test : {x : List Bool} → ι → InputBitData x → Bool)
    (hr : ∀ {x} i (d : InputBitData x), P i d →
      ReachesWithin M (d.cfg entry) {some yes, some no} (B x i) (E x i)
        (d.cfg (if test i d then yes else no)))
    (R : InputBitCall ι Q F D H) (T : InputBitCall ι V G A L)
    (hyes : ∀ {x} i (d : InputBitData x), P i d → test i d = true → Q i d)
    (hno : ∀ {x} i (d : InputBitData x), P i d → test i d = false → V i d) :
    InputBitCall ι P (fun i d => if test i d then F i d else G i d)
      (fun x i => B x i + 1 + D x i + A x i + 1)
      (fun x i => E x i + H x i + L x i) := by
  classical
  letI := R.finite
  letI := R.decEq
  letI := T.finite
  letI := T.decEq
  let e₁ : (S ⊕ R.S) ⊕ T.S := Sum.inl (Sum.inr R.exit)
  let e₂ : (S ⊕ R.S) ⊕ T.S := Sum.inr T.exit
  let X : Set (Option ((S ⊕ R.S) ⊕ T.S)) :=
    (Option.map (Sum.inl ∘ Sum.inr) '' {some R.exit}) ∪
      (Option.map Sum.inr '' {some T.exit})
  refine InputBitCall.close (seamCompTM₂ M yes no R.M R.entry T.M T.entry)
    (Sum.inl (Sum.inl entry)) X (by simp [X])
    (fun i d => if test i d then e₁ else e₂) ?_ ?_ ?_
  · intro x i d _
    by_cases h : test i d = true <;> simp [h, X, e₁, e₂]
  · intro x i d hp
    by_cases h : test i d = true
    · simpa only [if_pos h] using R.heads i d (hyes i d hp h)
    · simpa only [if_neg h] using T.heads i d (hno i d hp (Bool.eq_false_iff.mpr h))
  · intro x i d hp
    let C₀ : Contract M entry {some yes, some no} ι x := Contract.ofReaches
      (fun a c => P a (InputBitData.ofCfg c)) (fun a _ => B x a) (fun a _ => E x a)
      (fun a c => (InputBitData.ofCfg c).cfg (if test a (InputBitData.ofCfg c) then yes else no))
      (fun a c hc hP => by
        have h := hr a (InputBitData.ofCfg c) hP
        rw [InputBitData.cfg_ofCfg c entry hc] at h
        exact h)
      (fun a c _ _ => by
        change some (if test a (InputBitData.ofCfg c) then yes else no) ∈ {some yes, some no}
        split_ifs <;> simp)
    have h₁ : ∀ a c, c.state = some entry → C₀.pre a c →
        (C₀.post a c).state = some yes →
        (R.contract x).pre a ((C₀.post a c).mapState fun _ => R.entry) := by
      intro a c _ hP hs
      simp only [C₀, Contract.ofReaches_pre, Contract.ofReaches_post,
        InputBitCall.contract, InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] at hP hs ⊢
      apply hyes a _ hP
      by_contra h
      simp only [if_neg h, InputBitData.cfg, Option.some.injEq] at hs
      exact hne hs.symm
    have h₂ : ∀ a c, c.state = some entry → C₀.pre a c →
        (C₀.post a c).state = some no →
        (T.contract x).pre a ((C₀.post a c).mapState fun _ => T.entry) := by
      intro a c _ hP hs
      simp only [C₀, Contract.ofReaches_pre, Contract.ofReaches_post,
        InputBitCall.contract, InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] at hP hs ⊢
      apply hno a _ hP
      by_cases h : test a (InputBitData.ofCfg c) = true
      · simp only [if_pos h, InputBitData.cfg, Option.some.injEq] at hs
        exact (hne hs).elim
      · exact Bool.eq_false_iff.mpr h
    let C := Contract.branch hne C₀ (R.contract x) (T.contract x) id id h₁ h₂
    have hc : C.pre i (d.cfg (Sum.inl (Sum.inl entry))) := by
      simpa only [C, Contract.branch_pre, C₀, Contract.ofReaches_pre,
        InputBitData.ofCfg_mapState, InputBitData.ofCfg_cfg] using hp
    have ht₀ : C₀.time i (d.cfg entry) ≤ B x i :=
      Contract.ofReaches_time_le _ _ _ _ _ _ i _ rfl (by
        simpa only [InputBitData.ofCfg_cfg] using hp)
    have ht : C.time i (d.cfg (Sum.inl (Sum.inl entry))) ≤ B x i + 1 + D x i + A x i := by
      simp only [C, Contract.branch_time, C₀, Contract.ofReaches_post,
        InputBitData.cfg_mapState, InputBitData.ofCfg_cfg]
      by_cases h : test i d = true
      · have ht₁ := R.time_le i (d.cfg R.entry) rfl (by
          simpa only [InputBitData.ofCfg_cfg] using hyes i d hp h)
        simpa only [h, if_true, InputBitData.cfg, id_eq] using
          (Nat.add_le_add (Nat.add_le_add_right ht₀ 1) ht₁).trans (Nat.le_add_right _ _)
      · have hf : test i d = false := Bool.eq_false_iff.mpr h
        have ht₂ := T.time_le i (d.cfg T.entry) rfl (by
          simpa only [InputBitData.ofCfg_cfg] using hno i d hp hf)
        simpa only [hf, Bool.false_eq_true, if_false, InputBitData.cfg, Option.some.injEq,
          if_neg hne.symm, id_eq] using
          (Nat.add_le_add (Nat.add_le_add_right ht₀ 1) ht₂).trans
            (show B x i + 1 + A x i ≤ B x i + 1 + D x i + A x i by omega)
    rw [reachesWithin_iff]
    refine ⟨C.time i (d.cfg (Sum.inl (Sum.inl entry))), ht, ?_, ?_, ?_⟩
    · exact fun s hs => C.cut i _ rfl hc s hs
    · intro s hs j
      have h := C.env i (d.cfg (Sum.inl (Sum.inl entry))) rfl hc s hs j
      simp only [C, Contract.branch_lo, Contract.branch_hi, C₀, InputBitCall.contract,
        Contract.ofReaches_lo, Contract.ofReaches_hi, Contract.ofReaches_post,
        InputBitData.cfg_mapState, InputBitData.ofCfg_cfg, id_eq, Finset.mem_Icc] at h
      simp only [InputBitData.cfg] at h ⊢
      rw [abs_le]
      push_cast
      split_ifs at h <;> constructor <;> omega
    · have h := C.run i (d.cfg (Sum.inl (Sum.inl entry))) rfl hc
      simp only [C, Contract.branch_post, C₀, InputBitCall.contract, Contract.ofReaches_post,
        InputBitData.cfg_mapState, InputBitData.ofCfg_cfg, id_eq] at h
      rcases Bool.eq_false_or_eq_true (test i d) with hb | hb <;>
        simpa only [hb, Bool.false_eq_true, if_false, if_true, InputBitData.cfg,
          Option.some.injEq, if_neg hne.symm, e₁, e₂] using h

/-- Use a catalog contract with a bounded time as a head-returning call. -/
private def InputBitCall.ofContract {ι S : Type} [Fintype S] [DecidableEq S]
    {P : {x : List Bool} → ι → InputBitData x → Prop}
    {F : {x : List Bool} → ι → InputBitData x → InputBitData x}
    {B : List Bool → ι → ℕ} {M : MultiTapeTM 5 Bool S} {entry exit : S}
    {X : Set (Option S)} (C : (x : List Bool) → Contract M entry X ι x) (hx : some exit ∈ X)
    (hp : ∀ {x} i (d : InputBitData x), P i d → (C x).pre i (d.cfg entry))
    (hf : ∀ {x} i (d : InputBitData x), P i d → (C x).post i (d.cfg entry) = (F i d).cfg exit)
    (ht : ∀ {x} i (d : InputBitData x), P i d → (C x).time i (d.cfg entry) ≤ B x i)
    (hh : ∀ {x} i (d : InputBitData x), P i d → (F i d).workTapePos = d.workTapePos) :
    InputBitCall ι P F B B where
  S := S
  finite := inferInstance
  decEq := inferInstance
  M := M
  entry := entry
  exit := exit
  heads := hh
  reaches i d hP := by
    rw [reachesWithin_iff]
    refine ⟨(C _).time i (d.cfg entry), ht i d hP, ?_, ?_, ?_⟩
    · intro s hs he
      exact (C _).cut i _ rfl (hp i d hP) s hs (he.symm ▸ hx)
    · intro s hs j
      have h := (C _).time_envelope i (d.cfg entry) s hs j
      rw [Finset.mem_Icc] at h
      have hb := ht i d hP
      rw [abs_le]
      constructor <;> omega
    · exact ((C _).run i _ rfl (hp i d hP)).trans (hf i d hP)

/-! ## Private tape frames for the native call -/

/-- Install a globally delimited scratch word at tape three's current origin. -/
private def InputBitData.scratch {x : List Bool} (w : List Bool) (d : InputBitData x) :
    InputBitData x :=
  { d with
    workTapes := Function.update d.workTapes 3
      (fun z => FinTM.bufferTape w (z - d.workTapePos 3)) }

/-- Whether tape three globally holds a scratch word. -/
private def InputBitData.hasScratch {x : List Bool} (w : List Bool) (d : InputBitData x) : Prop :=
  ∀ z, d.workTapes 3 z = FinTM.bufferTape w (z - d.workTapePos 3)

/-- `WordAt` does not inspect the attached control state. -/
private theorem InputBitData.wordAt {x : List Bool} {S : Type} (d : InputBitData x) (s : S)
    (j : Fin 5) (w : List Bool) : WordAt (d.cfg s) j w ↔ WordAt (d.cfg ()) j w := by
  rw [wordAt_iff, wordAt_iff]
  rfl

/-- The scratch-tape predicate does not inspect the attached control state. -/
private theorem InputBitData.blank {x : List Bool} {S : Type} (d : InputBitData x) (s : S) :
    ScratchBlank (d.cfg s) ↔ ScratchBlank (d.cfg ()) := by
  rw [scratchBlank_iff, scratchBlank_iff]
  rfl

/-- A globally stored scratch word is delimited at its origin. -/
private theorem InputBitData.scratch_wordAt {x : List Bool} {S : Type} (d : InputBitData x)
    (s : S) (w : List Bool) (hw : d.hasScratch w) : WordAt (d.cfg s) 3 w := by
  rw [wordAt_iff]
  intro z _ _
  simpa only [InputBitData.cfg, add_sub_cancel_left] using hw (d.workTapePos 3 + z)

/-- Installing a scratch word satisfies its global specification. -/
private theorem InputBitData.hasScratch_scratch {x : List Bool} (w : List Bool)
    (d : InputBitData x) : (d.scratch w).hasScratch w := by
  intro z
  simp only [InputBitData.scratch, Function.update_self]

/-- A globally blank tape three is the empty scratch word. -/
private theorem InputBitData.hasScratch_nil {x : List Bool} (d : InputBitData x)
    (h : ∀ z, d.workTapes 3 z = none) : d.hasScratch [] := by
  intro z
  rw [h, FinTM.bufferTape_nil]

/-- Emptying an originally blank scratch tape recovers all physical fields. -/
private theorem InputBitData.scratch_nil {x : List Bool} (d : InputBitData x)
    (h : ∀ z, d.workTapes 3 z = none) : d.scratch [] = d := by
  have he : (fun z => FinTM.bufferTape ([] : List Bool) (z - d.workTapePos 3)) = d.workTapes 3 := by
    funext z
    rw [FinTM.bufferTape_nil, h]
  simp only [InputBitData.scratch, he, Function.update_eq_self]

/-- A second scratch installation keeps only the final word. -/
private theorem InputBitData.scratch_twice {x : List Bool} (u v : List Bool)
    (d : InputBitData x) : (d.scratch u).scratch v = d.scratch v := by
  simp only [InputBitData.scratch, Function.update_idem]

/-- Writing a same-width replacement over a globally stored word installs exactly the
new scratch word; writing the first word into an empty scratch tape does too.

**Proof sketch.** Read `wordWrite_apply`. On tape three's replacement interval it reads the
new buffer. Outside it both buffers are blank, by `FinTM.bufferTape_eq_none_of_not_mem`;
the old buffer is either empty or the same width. Every other tape is unchanged. -/
private theorem InputBitData.write_scratch {x : List Bool} (d : InputBitData x)
    (u v : List Bool) (hu : d.hasScratch u) (hlen : u = [] ∨ u.length = v.length) :
    wordWrite (d.cfg ()) 3 v = (d.scratch v).workTapes := by
  funext j z
  rw [wordWrite_apply]
  simp only [InputBitData.cfg, InputBitData.scratch]
  by_cases hj : j = 3
  · subst j
    simp only [Function.update_self, true_and]
    split_ifs with hz
    · rfl
    · rw [hu, FinTM.bufferTape_eq_none_of_not_mem v (z := z - d.workTapePos 3) (by omega)]
      rcases hlen with h | h
      · rw [h, FinTM.bufferTape_nil]
      · exact FinTM.bufferTape_eq_none_of_not_mem u (z := z - d.workTapePos 3) (by rw [h]; omega)
  · simp only [hj, false_and, if_false, Function.update_of_ne hj]

/-- The logical parameters shared by the calls in one input-read operation. -/
private structure InputBitArgs where
  width : ℕ
  index : BitVec width
  register : List Bool

/-- The external tape precondition, with the control state forgotten. -/
private def inputBitReady {x : List Bool} (i : InputBitArgs) (d : InputBitData x) : Prop :=
  WordAt (d.cfg ()) 0 (bvBits i.index) ∧ WordAt (d.cfg ()) 1 (Nat.bits x.length) ∧
    WordAt (d.cfg ()) 2 i.register ∧ i.register.length = i.width ∧ ScratchBlank (d.cfg ())

/-- Copy the position word to the globally blank scratch tape using the catalog row.

**Proof sketch.** Reindex `copyTM_contract` by the position's bits and apply
`InputBitCall.ofContract`. `InputBitData.write_scratch` identifies its framed endpoint with
a global scratch installation, and `bvBits_length` gives the linear time bound. -/
private def inputBitCopyCall : InputBitCall InputBitArgs
    (fun i d => WordAt (d.cfg ()) 0 (bvBits i.index) ∧ d.hasScratch [])
    (fun i d => d.scratch (bvBits i.index))
    (fun _ i => 2 * i.width + 2) (fun _ i => 2 * i.width + 2) :=
  InputBitCall.ofContract
    (fun x => inputBitContractOn (copyTM_contract 0 3 (by decide) x)
      (fun i : InputBitArgs => bvBits i.index) (fun _ _ => True)) (Set.mem_singleton _)
    (by
      intro x i d hp
      simp only [inputBitContractOn, copyTM_contract_pre]
      exact ⟨(wordAt_iff _ _ _).mp ((d.wordAt SweepPhase.sweep 0 _).mpr hp.1), trivial⟩)
    (by
      intro x i d hp
      apply Cfg.ext
      · simp only [inputBitContractOn, copyTM_contract_post, sweepPost_state, InputBitData.cfg]
      · simp only [inputBitContractOn, copyTM_contract_post, sweepPost_inputPos,
          InputBitData.cfg, InputBitData.scratch]
      · funext j z
        simp only [inputBitContractOn, copyTM_contract_post, sweepPost_workTapes,
          InputBitData.cfg]
        simpa only [wordWrite_apply, InputBitData.cfg] using
          congrFun (congrFun (d.write_scratch [] (bvBits i.index) hp.2 (Or.inl rfl)) j) z
      · funext j
        simp only [inputBitContractOn, copyTM_contract_post, sweepPost_workTapePos,
          InputBitData.cfg, InputBitData.scratch]
      · simp only [inputBitContractOn, copyTM_contract_post, sweepPost_output,
          InputBitData.cfg, InputBitData.scratch])
    (by intro x i d _; simp only [inputBitContractOn, copyTM_contract_time, bvBits_length]; rfl)
    (by intros; rfl)

/-- Increment the copied nonnegative positive-width position using the catalog counter.

**Proof sketch.** Reindex `incrementTM_contract` by the word and its successor.
`inputBitSuccBits_spec` supplies success and equal widths. The global scratch frame identifies
the endpoint. The carry-prefix sublist bounds the contract's time by twice the width plus two. -/
private def inputBitIncrementCall : InputBitCall InputBitArgs
    (fun i d => 0 < i.width ∧ 0 ≤ i.index.toInt ∧ d.hasScratch (bvBits i.index))
    (fun i d => d.scratch (inputBitSuccBits i.index))
    (fun _ i => 2 * i.width + 2) (fun _ i => 2 * i.width + 2) :=
  InputBitCall.ofContract
    (fun x => inputBitContractOn (incrementTM_contract 3 x)
      (fun i : InputBitArgs => (bvBits i.index, inputBitSuccBits i.index)) (fun _ _ => True))
    ⟨true, rfl⟩
    (by
      intro x i d hp
      simp only [inputBitContractOn, incrementTM_contract_pre]
      exact ⟨⟨(inputBitSuccBits_spec i.index hp.1 hp.2.1).1,
        (wordAt_iff _ _ _).mp (d.scratch_wordAt FlagPhase.run _ hp.2.2)⟩, trivial⟩)
    (by
      intro x i d hp
      have hlen := (inputBitSuccBits_spec i.index hp.1 hp.2.1).2.1
      apply Cfg.ext
      · simp only [inputBitContractOn, incrementTM_contract_post, InputBitData.cfg]
      · simp only [inputBitContractOn, incrementTM_contract_post, InputBitData.cfg,
          InputBitData.scratch]
      · funext j z
        simp only [inputBitContractOn, incrementTM_contract_post, InputBitData.cfg]
        have he : (inputBitSuccBits i.index).length = (bvBits i.index).length :=
          hlen.trans (bvBits_length i.index).symm
        simpa only [wordWrite_apply, InputBitData.cfg, he] using
          congrFun (congrFun (d.write_scratch (bvBits i.index) (inputBitSuccBits i.index)
            hp.2.2 (Or.inr he.symm)) j) z
      · simp only [inputBitContractOn, incrementTM_contract_post, InputBitData.cfg,
          InputBitData.scratch]
      · simp only [inputBitContractOn, incrementTM_contract_post, InputBitData.cfg,
          InputBitData.scratch])
    (by
      intro x i d _
      simp only [inputBitContractOn, incrementTM_contract_time]
      have h := List.takeWhile_sublist (p := id) (l := bvBits i.index)
      have h := h.length_le
      rw [bvBits_length] at h
      omega)
    (by intros; rfl)

/-- Clear the globally stored successor counter with the catalog's clearing sweep.

**Proof sketch.** Reindex `clearTM_contract` by the successor bits. Its precondition follows
from the global scratch frame. Inside its interval the endpoint is blank by the sweep's
equation; outside it the old scratch buffer is blank. The head-return and time clauses are
those of the catalog contract. -/
private def inputBitClearCall : InputBitCall InputBitArgs
    (fun i d => d.hasScratch (inputBitSuccBits i.index) ∧
      (inputBitSuccBits i.index).length = i.width)
    (fun _ d => d.scratch [])
    (fun _ i => 2 * i.width + 2) (fun _ i => 2 * i.width + 2) :=
  InputBitCall.ofContract
    (fun x => inputBitContractOn (clearTM_contract 3 x)
      (fun i : InputBitArgs => inputBitSuccBits i.index) (fun _ _ => True))
    (Set.mem_singleton _)
    (by
      intro x i d hp
      simp only [inputBitContractOn, clearTM_contract_pre]
      exact ⟨(wordAt_iff _ _ _).mp (d.scratch_wordAt SweepPhase.sweep _ hp.1), trivial⟩)
    (by
      intro x i d hp
      apply Cfg.ext
      · simp only [inputBitContractOn, clearTM_contract_post, sweepPost_state, InputBitData.cfg]
      · simp only [inputBitContractOn, clearTM_contract_post, sweepPost_inputPos,
          InputBitData.cfg, InputBitData.scratch]
      · funext j z
        simp only [inputBitContractOn, clearTM_contract_post, sweepPost_workTapes,
          InputBitData.cfg, InputBitData.scratch, FinTM.bufferTape_nil]
        by_cases hj : j = 3
        · subst j
          simp only [true_and, Function.update_self]
          split_ifs with hz
          · rfl
          · rw [hp.1]
            exact FinTM.bufferTape_eq_none_of_not_mem _ (by omega)
        · simp only [hj, false_and, if_false, Function.update_of_ne hj]
      · funext j
        simp only [inputBitContractOn, clearTM_contract_post, sweepPost_workTapePos,
          InputBitData.cfg, InputBitData.scratch]
      · simp only [inputBitContractOn, clearTM_contract_post, sweepPost_output,
          InputBitData.cfg, InputBitData.scratch])
    (by intro x i d hp; simp only [inputBitContractOn, clearTM_contract_time, hp.2]; rfl)
    (by intros; rfl)

/-- Replace the register by a Boolean integer constant, leaving its surroundings framed. -/
private def inputBitWrite {x : List Bool} (b : Bool) (i : InputBitArgs) (d : InputBitData x) :
    InputBitData x :=
  { d with workTapes := wordWrite (d.cfg ()) 2 (bvBits (if b then (1 : BitVec i.width) else 0)) }

/-- The permitted integer-constant row supplies each branch's register writer.

**Proof sketch.** Choose `exists_wordIntTM` for the Boolean integer and zero added width.
Read the ready register and blank scratch through the state-independent adapters. The public
word-write equation and `BitVec.ofInt_ofNat` identify its endpoint with `inputBitWrite`. -/
private theorem inputBitConstantCall (b : Bool) : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun i d => WordAt (d.cfg ()) 2 i.register ∧ i.register.length = i.width ∧
      ScratchBlank (d.cfg ()))
    (inputBitWrite b) (fun _ i => C * (i.width + 1)) (fun _ i => C * (i.width + 1))) := by
  obtain ⟨S, hS, hD, M, entry, exit, C, hM⟩ := exists_wordIntTM (if b then 1 else 0) 0
  refine ⟨C, ⟨⟨S, hS, hD, M, entry, exit, (by intros; rfl), ?_⟩⟩⟩
  intro x i d hp
  have h := hM (W := i.width) i.register (d.cfg entry) rfl
    ((d.wordAt entry 2 _).mpr hp.1) (by simpa only [Nat.add_zero] using hp.2.1)
    ((d.blank entry).mpr hp.2.2)
  have he : { d.cfg entry with
      state := some exit
      workTapes := wordWrite (d.cfg entry) 2
        (bvBits (BitVec.ofInt (i.width + 0) (if b then 1 else 0))) } =
      (inputBitWrite b i d).cfg exit := by
    cases b <;> apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
      simp only [inputBitWrite, InputBitData.cfg, wordWrite_apply, Bool.false_eq_true,
        if_false, if_true, Nat.add_zero, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat]
  rw [he] at h
  exact h

/-- The in-range case of a positive-width, nonnegative signed index. -/
private def inputBitCanRead (x : List Bool) (i : InputBitArgs) : Prop :=
  0 < i.width ∧ 0 ≤ i.index.toInt ∧ i.index.toInt.toNat < x.length

/-- Move the input head to the index's shifted input position; outside the intended
precondition the minimum merely keeps the configuration well typed. -/
private def inputBitSeek {x : List Bool} (i : InputBitArgs) (d : InputBitData x) : InputBitData x :=
  { d with inputPos := ⟨min (i.index.toInt.toNat + 1) (x.length + 1), by
      have h := min_le_right (i.index.toInt.toNat + 1) (x.length + 1); omega⟩ }

/-- Place the restored two-tape native seek on scratch tapes three and four.

**Proof sketch.** Choose `inputBit_exists_seek_row` and embed its two tapes with
`embedEmitTM`. The source configuration is the selected physical bank, with empty output;
`embedEmitCfg_eq` reconstructs the host both before and after the run. Selected heads satisfy
the native row's envelope, and `embedEmitCfg_unselected` fixes every other head. The successor
counter has width `W` and value `u + 1`, and both native input positions are at most `n + 1`,
so the native time is at most `3C(W + n + 1)`, while its work radius stays `C(W + 1)`. -/
private theorem inputBitSeekCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun {x} i d => inputBitCanRead x i ∧ d.hasScratch (inputBitSuccBits i.index) ∧
      ∀ z, d.workTapes 4 z = none)
    inputBitSeek (fun x i => 3 * C * (i.width + x.length + 1))
      (fun _ i => C * (i.width + 1))) := by
  obtain ⟨S, hS, hD, M, entry, exit, C, hM⟩ := inputBit_exists_seek_row
  let σ : Fin 2 ↪ Fin 5 := Fin.natAddEmb 3
  refine ⟨C, ⟨⟨S, hS, hD, embedEmitTM σ M, entry, exit, (by intros; rfl), ?_⟩⟩⟩
  intro x i d hp
  let p := i.index.toInt.toNat + 1
  have hpx : p ≤ x.length + 1 := by have h := hp.1.2.2; omega
  have hspec := inputBitSuccBits_spec i.index hp.1.1 hp.1.2.1
  let c : Cfg 2 Bool S x := ⟨some entry, d.inputPos, fun j => d.workTapes (σ j),
    fun j => d.workTapePos (σ j), []⟩
  have hw : WordAt c 0 (inputBitSuccBits i.index) := by
    rw [wordAt_iff]
    intro z _ _
    change d.workTapes 3 (d.workTapePos 3 + z) = _
    simpa only [add_sub_cancel_left] using hp.2.1 (d.workTapePos 3 + z)
  have hb : ∀ z, c.workTapes 1 z = none := hp.2.2
  have hr := hM p (inputBitSuccBits i.index) hspec.2.2 hpx c rfl hw hb
  rw [reachesWithin_iff] at hr
  obtain ⟨t, ht, hcut, henv, hrun⟩ := hr
  have hstart : embedEmitCfg σ d.workTapes d.workTapePos d.output c = d.cfg entry :=
    embedEmitCfg_eq σ _ _ _ c _ rfl rfl (List.append_nil _) (fun _ => ⟨rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩)
  have htrace (u : ℕ) : (embedEmitTM σ M).runFrom (d.cfg entry) u =
      embedEmitCfg σ d.workTapes d.workTapePos d.output (M.runFrom c u) := by
    rw [← hstart, embedEmitTM_runFrom]
  rw [reachesWithin_iff]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · have hip := d.inputPos.isLt
    have hlen := hspec.2.1
    change t ≤ 3 * C * (i.width + x.length + 1)
    apply ht.trans
    calc
      C * ((inputBitSuccBits i.index).length + c.inputPos.val + p + 1) ≤
          C * (3 * (i.width + x.length + 1)) := by
            apply Nat.mul_le_mul_left
            change (inputBitSuccBits i.index).length + d.inputPos.val + p + 1 ≤ _
            omega
      _ = 3 * C * (i.width + x.length + 1) := by ring
  · intro u hu he
    apply hcut u hu
    rw [htrace, embedEmitCfg_state] at he
    exact he
  · intro u hu j
    rw [htrace]
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨a, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos]
      have h := henv u hu a
      simpa only [c, InputBitData.cfg, hspec.2.1] using h
    · rw [(embedEmitCfg_unselected σ _ _ _ _ j hj).2]
      simp only [InputBitData.cfg, sub_self, abs_zero, Nat.cast_nonneg]
  · rw [htrace, hrun]
    apply embedEmitCfg_eq σ _ _ _ _ _ rfl
    · apply Fin.ext
      change p = min p (x.length + 1)
      rw [Nat.min_eq_left hpx]
    · exact List.append_nil _
    · exact fun _ => ⟨rfl, rfl⟩
    · exact fun _ _ => ⟨rfl, rfl⟩

/-- A scratch installation commutes with the input-only head change. -/
private theorem inputBitSeek_scratch {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (w : List Bool) : inputBitSeek i (d.scratch w) = (inputBitSeek i d).scratch w := rfl

/-- Seeking does not change the work-tape precondition. -/
private theorem inputBitReady_seek {x : List Bool} (i : InputBitArgs) (d : InputBitData x) :
    inputBitReady i (inputBitSeek i d) ↔ inputBitReady i d := by
  simp only [inputBitReady, wordAt_iff, scratchBlank_iff, inputBitSeek, InputBitData.cfg]

/-- The whole valid-index seek: copy, increment, native seek, and erase the scratch counter.

**Proof sketch.** Strengthen `inputBitCopyCall` to the ready, valid-index precondition and
compose it with `inputBitIncrementCall`, `inputBitSeekCall` and `inputBitClearCall` through
`InputBitCall.seq`. The global scratch predicates discharge each link. Successive installations
collapse by `InputBitData.scratch_twice`, and clearing recovers the initially blank tape by
`InputBitData.scratch_nil`. Sum the four time and radius bounds and enlarge the coefficient. -/
private theorem inputBitValidSeekCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun {x} i d => inputBitReady i d ∧ inputBitCanRead x i)
    inputBitSeek (fun x i => C * (i.width + x.length + 1))
      (fun _ i => C * (i.width + 1))) := by
  obtain ⟨C, ⟨seek⟩⟩ := inputBitSeekCall
  let P : {x : List Bool} → InputBitArgs → InputBitData x → Prop :=
    fun {x} i d => inputBitReady i d ∧ inputBitCanRead x i
  let cp : InputBitCall InputBitArgs P (fun i d => d.scratch (bvBits i.index))
      (fun _ i => 2 * i.width + 2) (fun _ i => 2 * i.width + 2) :=
    inputBitCopyCall.adapt (by
      intro x i d hp
      refine ⟨hp.1.1, d.hasScratch_nil ?_⟩
      exact (scratchBlank_iff _).mp hp.1.2.2.2.2 3 (by decide))
      (by intros; rfl) (by intros; rfl) (by intros; rfl)
  let inc := cp.seq inputBitIncrementCall (by
    intro x i d hp
    exact ⟨hp.2.1, hp.2.2.1, d.hasScratch_scratch _⟩)
  let sk := inc.seq seek (by
    intro x i d hp
    refine ⟨hp.2, (d.scratch _).hasScratch_scratch _, ?_⟩
    intro z
    simp only [InputBitData.scratch, Function.update_of_ne (by decide : (4 : Fin 5) ≠ 3)]
    exact (scratchBlank_iff _).mp hp.1.2.2.2.2 4 (by decide) z)
  let all := sk.seq inputBitClearCall (by
    intro x i d hp
    refine ⟨?_, (inputBitSuccBits_spec i.index hp.2.1 hp.2.2.1).2.1⟩
    simpa only [inputBitSeek, InputBitData.hasScratch] using
      (d.scratch (bvBits i.index)).hasScratch_scratch (inputBitSuccBits i.index))
  refine ⟨10 + 3 * C, ⟨all.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d hp
    change (inputBitSeek i ((d.scratch (bvBits i.index)).scratch
      (inputBitSuccBits i.index))).scratch [] = inputBitSeek i d
    rw [InputBitData.scratch_twice, inputBitSeek_scratch, InputBitData.scratch_twice,
      ← inputBitSeek_scratch, InputBitData.scratch_nil]
    exact (scratchBlank_iff _).mp hp.1.2.2.2.2 3 (by decide)
  · intro x i
    change 2 * i.width + 2 + 1 + (2 * i.width + 2) + 1 +
      3 * C * (i.width + x.length + 1) + 1 + (2 * i.width + 2) ≤
        (10 + 3 * C) * (i.width + x.length + 1)
    simp only [Nat.add_mul]
    omega
  · intro x i
    change 2 * i.width + 2 + (2 * i.width + 2) + C * (i.width + 1) + (2 * i.width + 2) ≤
      (10 + 3 * C) * (i.width + 1)
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega

/-- The bit currently under the native input head, with blanks read as false. -/
private def inputBitNativeBit {x : List Bool} (d : InputBitData x) : Bool :=
  ((d.cfg ()).inputSymbol).getD false

/-- A one-step native-input test. No catalog row returns a Boolean native-input read as a
verdict without moving a head; this leaf only uses the published stationary input action. -/
private def inputBitReadTM : MultiTapeTM 5 Bool FlagPhase where
  q₀ := .run
  tr := fun q inp _ => match q with
    | .run => inputMoveAction 0 (.done (inp.getD false))
    | .rewind b => inputMoveAction 0 (.rewind b)
    | .done b => inputMoveAction 0 (.done b)

/-- Read the native bit without changing any physical field.

**Proof sketch.** `step_of_inputMoveAction` gives the single stationary read step. The only
earlier time is zero, when the state is the distinct entry constructor. At times zero and one
the physical heads are unchanged. -/
private theorem inputBitRead_reaches {x : List Bool} (d : InputBitData x) :
    ReachesWithin inputBitReadTM (d.cfg FlagPhase.run)
      {some (FlagPhase.done true), some (FlagPhase.done false)} 1 1
      (d.cfg (if inputBitNativeBit d then FlagPhase.done true else FlagPhase.done false)) := by
  have hs : inputBitReadTM.runFrom (d.cfg FlagPhase.run) 1 =
      d.cfg (FlagPhase.done (inputBitNativeBit d)) := by
    rw [MultiTapeTM.runFrom_one, step_of_inputMoveAction inputBitReadTM _ 0 rfl rfl,
      moveInputPos_zero]
    have he := Cfg.inputSymbol_congr (d.cfg FlagPhase.run) (d.cfg ()) rfl
    simp only [InputBitData.cfg, inputBitNativeBit] at he ⊢
    rw [he]
  rw [reachesWithin_iff]
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · intro s h he
    obtain rfl : s = 0 := by omega
    simp [InputBitData.cfg] at he
  · intro s h j
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp only [MultiTapeTM.runFrom_zero, InputBitData.cfg, sub_self, abs_zero,
        Nat.cast_one, zero_le_one]
    · rw [hs]
      simp only [InputBitData.cfg, sub_self, abs_zero, Nat.cast_one, zero_le_one]
  · rw [hs]
    cases inputBitNativeBit d <;> rfl

/-- The shifted seek position reads precisely the requested list digit. -/
private theorem inputBitNativeBit_seek {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hi : inputBitCanRead x i) :
    inputBitNativeBit (inputBitSeek i d) = x.getD i.index.toInt.toNat false := by
  rw [inputBitNativeBit, FinTM.inputSymbol_at _ i.index.toInt.toNat (by have h := hi.2.2; omega)]
  · rw [List.getD_eq_getElem?_getD]
  · change min (i.index.toInt.toNat + 1) (x.length + 1) = i.index.toInt.toNat + 1
    exact min_eq_left (by have h := hi.2.2; omega)

/-- Derive a read-only verdict row from a catalog contract and its endpoint equation.

**Proof sketch.** Use the contract's run and cut, with each advertised verdict in its exit set.
`Contract.time_envelope` and the time bound supply the radius. The supplied endpoint equation
then gives the physical read-only result. -/
private theorem inputBitTest_ofContract {ι S : Type}
    {P : {x : List Bool} → ι → InputBitData x → Prop}
    {B : List Bool → ι → ℕ} {M : MultiTapeTM 5 Bool S} {entry yes no : S}
    {X : Set (Option S)} (C : (x : List Bool) → Contract M entry X ι x)
    (hy : some yes ∈ X) (hn : some no ∈ X)
    (test : {x : List Bool} → ι → InputBitData x → Bool)
    (hp : ∀ {x} i (d : InputBitData x), P i d → (C x).pre i (d.cfg entry))
    (hf : ∀ {x} i (d : InputBitData x), P i d →
      (C x).post i (d.cfg entry) = d.cfg (if test i d then yes else no))
    (ht : ∀ {x} i (d : InputBitData x), P i d → (C x).time i (d.cfg entry) ≤ B x i)
    {x : List Bool} (i : ι) (d : InputBitData x) (hP : P i d) :
    ReachesWithin M (d.cfg entry) {some yes, some no} (B x i) (B x i)
      (d.cfg (if test i d then yes else no)) := by
  rw [reachesWithin_iff]
  refine ⟨(C x).time i (d.cfg entry), ht i d hP, ?_, ?_, ?_⟩
  · intro s hs he
    apply (C x).cut i _ rfl (hp i d hP) s hs
    rcases he with he | he
    · exact he ▸ hy
    · exact he ▸ hn
  · intro s hs j
    have h := (C x).time_envelope i (d.cfg entry) s hs j
    rw [Finset.mem_Icc] at h
    have hb := ht i d hP
    rw [abs_le]
    constructor <;> omega
  · exact ((C x).run i _ rfl (hp i d hP)).trans (hf i d hP)

/-- The catalog equality comparator detects width zero by comparing with blank scratch.

**Proof sketch.** Reindex `compareTM_contract` by the source bits and the empty scratch word.
Its equality verdict is the width test by `bvBits_length`; its stop is zero by `compareStop_le`.
Apply `inputBitTest_ofContract` to its precondition, endpoint and bounded time. -/
private theorem inputBitWidth_reaches {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hp : inputBitReady i d) :
    ReachesWithin (compareTM 5 0 3) (d.cfg FlagPhase.run)
      {some (FlagPhase.done true), some (FlagPhase.done false)} (2 * i.width + 2)
      (2 * i.width + 2) (d.cfg (if decide (i.width = 0) then .done true else .done false)) := by
  apply inputBitTest_ofContract
    (fun x => inputBitContractOn (compareTM_contract 0 3 (by decide) x)
      (fun i : InputBitArgs => (bvBits i.index, [])) (fun _ _ => True))
    ⟨true, rfl⟩ ⟨false, rfl⟩ (fun i _ => decide (i.width = 0))
    (P := fun i d => inputBitReady i d) (B := fun _ i => 2 * i.width + 2)
    (by
      intro x i d hP
      simp only [inputBitContractOn, compareTM_contract_pre]
      refine ⟨⟨(wordAt_iff _ _ _).mp ((d.wordAt _ _ _).mpr hP.1), ?_⟩, trivial⟩
      exact (wordAt_iff _ _ _).mp (d.scratch_wordAt _ [] (d.hasScratch_nil
        ((scratchBlank_iff _).mp hP.2.2.2.2 3 (by decide)))))
    (by
      intro x i d _
      have he : bvBits i.index = [] ↔ i.width = 0 := by
        rw [← List.length_eq_zero_iff, bvBits_length]
      simp only [inputBitContractOn, compareTM_contract_post, he]
      by_cases h : i.width = 0 <;> simp [h, InputBitData.cfg])
    (by
      intro x i d _
      simp only [inputBitContractOn, compareTM_contract_time]
      have h := compareStop_le (bvBits i.index) ([] : List Bool)
      simp only [List.length_nil, Nat.min_zero] at h
      omega)
    i d hp

/-- Unsigned tape comparison agrees with the signed natural index when its sign is clear. -/
private theorem inputBitOrder_index {x : List Bool} (i : InputBitArgs)
    (hi : 0 ≤ i.index.toInt) :
    inputBitOrder false (bvBits i.index) (Nat.bits x.length) = true ↔
      i.index.toInt.toNat < x.length := by
  rw [inputBitOrder_lt, inputBit_bvBits_value,
    (counterValue_eq _).symm.trans (counterValue_bits x.length),
    ← BitVec.toNat_toInt_of_msb i.index
      (BitVec.msb_eq_false_iff_two_mul_lt.mpr (BitVec.toInt_pos_iff.mp hi))]

/-- Read the current native bit and write its Boolean word using the two constant rows.

**Proof sketch.** Branch on `inputBitReadTM` into `inputBitConstantCall true` or
`inputBitConstantCall false`, both of which use only the ready register and blank scratch.
The selected endpoint is `inputBitWrite` of the read bit; sum the coefficients and dispatches. -/
private theorem inputBitReadWriteCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    inputBitReady (fun i d => inputBitWrite (inputBitNativeBit d) i d)
    (fun _ i => C * (i.width + 1)) (fun _ i => C * (i.width + 1))) := by
  obtain ⟨C₁, ⟨one⟩⟩ := inputBitConstantCall true
  obtain ⟨C₀, ⟨zero⟩⟩ := inputBitConstantCall false
  let R := InputBitCall.branch inputBitReadTM .run (.done true) (.done false) (by intro h; cases h)
    (fun _ d => inputBitNativeBit d) (P := inputBitReady)
    (B := fun _ _ => 1) (E := fun _ _ => 1)
    (by intro x i d _; exact inputBitRead_reaches d) one zero
    (by intro x i d hp _; exact ⟨hp.2.2.1, hp.2.2.2⟩)
    (by intro x i d hp _; exact ⟨hp.2.2.1, hp.2.2.2⟩)
  refine ⟨C₁ + C₀ + 3, ⟨R.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d _
    change (if inputBitNativeBit d then inputBitWrite true i d else inputBitWrite false i d) = _
    cases inputBitNativeBit d <;> rfl
  · intro x i
    change 1 + 1 + C₁ * (i.width + 1) + C₀ * (i.width + 1) + 1 ≤
      (C₁ + C₀ + 3) * (i.width + 1)
    simp only [Nat.add_mul]
    omega
  · intro x i
    change 1 + C₁ * (i.width + 1) + C₀ * (i.width + 1) ≤ (C₁ + C₀ + 3) * (i.width + 1)
    simp only [Nat.add_mul]
    omega

/-- The Boolean answer specified by a signed input read. -/
private def inputBitAnswer (x : List Bool) (i : InputBitArgs) : Bool :=
  decide (0 ≤ i.index.toInt ∧ x.getD i.index.toInt.toNat false = true)

/-- The finished physical data, retaining whichever input position the selected path used. -/
private noncomputable def inputBitResult {x : List Bool} (i : InputBitArgs)
    (d : InputBitData x) : InputBitData x := by
  classical
  exact inputBitWrite (inputBitAnswer x i) i (if inputBitCanRead x i then inputBitSeek i d else d)

/-- With a nonnegative index, the Boolean answer is the requested list digit. -/
private theorem inputBitAnswer_nonneg {x : List Bool} (i : InputBitArgs)
    (hi : 0 ≤ i.index.toInt) : inputBitAnswer x i = x.getD i.index.toInt.toNat false := by
  simp [inputBitAnswer, hi]

/-- Negative indices take the zero-writing path without seeking. -/
private theorem inputBitResult_negative {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hi : i.index.toInt < 0) : inputBitResult i d = inputBitWrite false i d := by
  have hn : ¬ 0 ≤ i.index.toInt := by omega
  simp only [inputBitResult, inputBitCanRead, inputBitAnswer, hn, false_and, and_false,
    if_false, decide_false]

/-- An index past the input takes the zero-writing path without seeking. -/
private theorem inputBitResult_past {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hi : x.length ≤ i.index.toInt.toNat) : inputBitResult i d = inputBitWrite false i d := by
  have hd : x.getD i.index.toInt.toNat false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have hn : ¬ i.index.toInt.toNat < x.length := by omega
  simp only [inputBitResult, inputBitCanRead, inputBitAnswer, hn, hd, Bool.false_eq_true,
    and_false, if_false, decide_false]

/-- At width zero every Boolean constant is the same empty register word. -/
private theorem inputBitWrite_width_zero {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hW : i.width = 0) (b : Bool) : inputBitWrite b i d = inputBitWrite false i d := by
  haveI : Subsingleton (BitVec i.width) := by rw [hW]; infer_instance
  have h : (if b then (1 : BitVec i.width) else 0) = (0 : BitVec i.width) := Subsingleton.elim _ _
  simp only [inputBitWrite, h, Bool.false_eq_true, if_false]

/-- The width-zero branch can always write zero. -/
private theorem inputBitResult_width_zero {x : List Bool} (i : InputBitArgs) (d : InputBitData x)
    (hW : i.width = 0) : inputBitResult i d = inputBitWrite false i d := by
  have hn : ¬ inputBitCanRead x i := by intro h; have h := h.1; omega
  simp only [inputBitResult, if_neg hn]
  exact inputBitWrite_width_zero i d hW _

/-- A complete valid-index input read, with scratch already cleared before the bit test.

**Proof sketch.** Sequence `inputBitValidSeekCall` and `inputBitReadWriteCall`. The work-tape
precondition survives the seek by `inputBitReady_seek`. The endpoint becomes
`inputBitResult` by `inputBitNativeBit_seek` and `inputBitAnswer_nonneg`. Enlarge the sum of the
linear bounds to one coefficient, keeping the work radius linear in the width alone. -/
private theorem inputBitValidReadCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun {x} i d => inputBitReady i d ∧ inputBitCanRead x i)
    inputBitResult (fun x i => C * (i.width + x.length + 1))
      (fun _ i => C * (i.width + 1))) := by
  obtain ⟨C₁, ⟨seek⟩⟩ := inputBitValidSeekCall
  obtain ⟨C₂, ⟨write⟩⟩ := inputBitReadWriteCall
  let R := seek.seq write (by
    intro x i d hp
    exact (inputBitReady_seek i d).mpr hp.1)
  refine ⟨C₁ + C₂ + 1, ⟨R.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d hp
    change inputBitWrite (inputBitNativeBit (inputBitSeek i d)) i (inputBitSeek i d) = _
    rw [inputBitNativeBit_seek i d hp.2]
    simp only [inputBitResult, if_pos hp.2, inputBitAnswer_nonneg i hp.2.2.1]
  · intro x i
    change C₁ * (i.width + x.length + 1) + 1 + C₂ * (i.width + 1) ≤
      (C₁ + C₂ + 1) * (i.width + x.length + 1)
    have h := Nat.mul_le_mul_left C₂ (show i.width + 1 ≤ i.width + x.length + 1 by omega)
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · intro x i
    change C₁ * (i.width + 1) + C₂ * (i.width + 1) ≤ (C₁ + C₂ + 1) * (i.width + 1)
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- The range decision: read a valid index and write zero for a position past the input.

**Proof sketch.** Branch on `inputBitCompareTM`, whose restored numeric verdict is
`inputBitOrder_index`. The true branch is `inputBitValidReadCall`; the false branch is the
zero constant writer, identified with `inputBitResult` by `inputBitResult_past`. Bound the
comparison's binary-length time by the input length using `length_bits_le_self`; its radius
retains the binary length. Sum the branch coefficients with the dispatch steps. -/
private theorem inputBitRangeCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun i d => inputBitReady i d ∧ 0 < i.width ∧ 0 ≤ i.index.toInt)
    inputBitResult (fun x i => C * (i.width + x.length + 1))
      (fun x i => C * (i.width + (Nat.bits x.length).length + 1))) := by
  obtain ⟨Cᵥ, ⟨valid⟩⟩ := inputBitValidReadCall
  obtain ⟨C₀, ⟨zero⟩⟩ := inputBitConstantCall false
  let P : {x : List Bool} → InputBitArgs → InputBitData x → Prop :=
    fun i d => inputBitReady i d ∧ 0 < i.width ∧ 0 ≤ i.index.toInt
  let test : {x : List Bool} → InputBitArgs → InputBitData x → Bool :=
    fun {x} i _ => inputBitOrder false (bvBits i.index) (Nat.bits x.length)
  have hr : ∀ {x} i (d : InputBitData x), P i d →
      ReachesWithin inputBitCompareTM (d.cfg inputBitCompareEntry)
        {some (inputBitCompareExit true), some (inputBitCompareExit false)}
        (10 * (i.width + (Nat.bits x.length).length + 1))
        (10 * (i.width + (Nat.bits x.length).length + 1))
        (d.cfg (if test i d then inputBitCompareExit true else inputBitCompareExit false)) := by
    intro x i d hp
    have h := inputBitCompare_reaches (d.cfg inputBitCompareEntry) (bvBits i.index)
      (Nat.bits x.length) rfl ((d.wordAt _ _ _).mpr hp.1.1)
      ((d.wordAt _ _ _).mpr hp.1.2.1)
    have he : { d.cfg inputBitCompareEntry with
        state := some (inputBitCompareExit (test i d)) } =
        d.cfg (if test i d then inputBitCompareExit true else inputBitCompareExit false) := by
      rcases Bool.eq_false_or_eq_true (test i d) with h | h <;> simp [h, InputBitData.cfg]
    rw [bvBits_length, Set.pair_comm] at h
    rw [← he]
    exact h
  let R := InputBitCall.branch inputBitCompareTM inputBitCompareEntry
    (inputBitCompareExit true) (inputBitCompareExit false) (by decide) test hr valid zero
    (by
      intro x i d hp ht
      exact ⟨hp.1, hp.2.1, hp.2.2, (inputBitOrder_index i hp.2.2).mp ht⟩)
    (by intro x i d hp _; exact ⟨hp.1.2.2.1, hp.1.2.2.2⟩)
  refine ⟨10 + Cᵥ + C₀ + 2, ⟨R.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d hp
    change (if test i d then inputBitResult i d else inputBitWrite false i d) = inputBitResult i d
    by_cases ht : test i d = true
    · rw [if_pos ht]
    · rw [if_neg ht]
      have hn : ¬ i.index.toInt.toNat < x.length := fun h =>
        ht ((inputBitOrder_index i hp.2.2).mpr h)
      exact (inputBitResult_past i d (by omega)).symm
  · intro x i
    change 10 * (i.width + (Nat.bits x.length).length + 1) + 1 +
      Cᵥ * (i.width + x.length + 1) + C₀ * (i.width + 1) + 1 ≤
        (10 + Cᵥ + C₀ + 2) * (i.width + x.length + 1)
    have hb := length_bits_le_self x.length
    have h₁ := Nat.mul_le_mul_left 10
      (show i.width + (Nat.bits x.length).length + 1 ≤ i.width + x.length + 1 by omega)
    have h₂ := Nat.mul_le_mul_left C₀ (show i.width + 1 ≤ i.width + x.length + 1 by omega)
    simp only [Nat.add_mul]
    omega
  · intro x i
    change 10 * (i.width + (Nat.bits x.length).length + 1) + Cᵥ * (i.width + 1) +
      C₀ * (i.width + 1) ≤ (10 + Cᵥ + C₀ + 2) * (i.width + (Nat.bits x.length).length + 1)
    have h₁ := Nat.mul_le_mul_left Cᵥ
      (show i.width + 1 ≤ i.width + (Nat.bits x.length).length + 1 by omega)
    have h₂ := Nat.mul_le_mul_left C₀
      (show i.width + 1 ≤ i.width + (Nat.bits x.length).length + 1 by omega)
    simp only [Nat.add_mul]
    omega

/-- The signed decision: a negative index writes zero, and a nonnegative index tests its range.

**Proof sketch.** Choose the permitted `exists_wordSignTM` row and branch with
`InputBitCall.branch`. A negative verdict is `inputBitResult_negative`; a nonnegative verdict
meets `inputBitRangeCall`'s precondition. Both continuations restore all work heads. Enlarge
their summed time and radius bounds to one coefficient. -/
private theorem inputBitSignCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    (fun i d => inputBitReady i d ∧ 0 < i.width)
    inputBitResult (fun x i => C * (i.width + x.length + 1))
      (fun x i => C * (i.width + (Nat.bits x.length).length + 1))) := by
  obtain ⟨Cᵣ, ⟨range⟩⟩ := inputBitRangeCall
  obtain ⟨C₀, ⟨zero⟩⟩ := inputBitConstantCall false
  obtain ⟨S, hS, hD, M, entry, yes, no, Cₛ, hne, hM⟩ := exists_wordSignTM
  letI := hS
  letI := hD
  let R := InputBitCall.branch M entry yes no hne
    (fun i _ => decide (i.index.toInt < 0)) (P := fun i d => inputBitReady i d ∧ 0 < i.width)
    (B := fun _ i => Cₛ * (i.width + 1)) (E := fun _ i => Cₛ * (i.width + 1))
    (by
      intro x i d hp
      have h := hM i.index (d.cfg entry) rfl ((d.wordAt _ _ _).mpr hp.1.1)
        ((d.blank _).mpr hp.1.2.2.2.2)
      simpa only [InputBitData.cfg, decide_eq_true_eq] using h)
    zero range
    (by intro x i d hp _; exact ⟨hp.1.2.2.1, hp.1.2.2.2⟩)
    (by
      intro x i d hp hn
      have hn := of_decide_eq_false hn
      exact ⟨hp.1, hp.2, by omega⟩)
  refine ⟨Cₛ + C₀ + Cᵣ + 2, ⟨R.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d _
    change (if decide (i.index.toInt < 0) then inputBitWrite false i d else inputBitResult i d) = _
    by_cases hn : i.index.toInt < 0
    · simp only [decide_eq_true hn, if_true, inputBitResult_negative i d hn]
    · simp only [decide_eq_false hn, Bool.false_eq_true, if_false]
  · intro x i
    change Cₛ * (i.width + 1) + 1 + C₀ * (i.width + 1) +
      Cᵣ * (i.width + x.length + 1) + 1 ≤ (Cₛ + C₀ + Cᵣ + 2) * (i.width + x.length + 1)
    have h₁ := Nat.mul_le_mul_left Cₛ (show i.width + 1 ≤ i.width + x.length + 1 by omega)
    have h₂ := Nat.mul_le_mul_left C₀ (show i.width + 1 ≤ i.width + x.length + 1 by omega)
    simp only [Nat.add_mul]
    omega
  · intro x i
    change Cₛ * (i.width + 1) + C₀ * (i.width + 1) +
      Cᵣ * (i.width + (Nat.bits x.length).length + 1) ≤
        (Cₛ + C₀ + Cᵣ + 2) * (i.width + (Nat.bits x.length).length + 1)
    have h₁ := Nat.mul_le_mul_left Cₛ
      (show i.width + 1 ≤ i.width + (Nat.bits x.length).length + 1 by omega)
    have h₂ := Nat.mul_le_mul_left C₀
      (show i.width + 1 ≤ i.width + (Nat.bits x.length).length + 1 by omega)
    simp only [Nat.add_mul]
    omega

/-- The full reader call, including the empty-width boundary case.

**Proof sketch.** `inputBitWidth_reaches` compares the source with empty scratch. If its width
is zero, the zero writer suffices by `inputBitResult_width_zero`. Otherwise invoke
`inputBitSignCall`. Compose through `InputBitCall.branch` and combine the linear bounds. -/
private theorem inputBitFullCall : ∃ C : ℕ, Nonempty (InputBitCall InputBitArgs
    inputBitReady inputBitResult (fun x i => C * (i.width + x.length + 1))
      (fun x i => C * (i.width + (Nat.bits x.length).length + 1))) := by
  obtain ⟨Cₛ, ⟨sign⟩⟩ := inputBitSignCall
  obtain ⟨C₀, ⟨zero⟩⟩ := inputBitConstantCall false
  let R := InputBitCall.branch (compareTM 5 0 3) .run (.done true) (.done false) (by intro h; cases h)
    (fun i _ => decide (i.width = 0)) (P := inputBitReady)
    (B := fun _ i => 2 * i.width + 2) (E := fun _ i => 2 * i.width + 2)
    (by intro x i d hp; exact inputBitWidth_reaches i d hp) zero sign
    (by intro x i d hp _; exact ⟨hp.2.2.1, hp.2.2.2⟩)
    (by intro x i d hp hn; have hn := of_decide_eq_false hn; exact ⟨hp, by omega⟩)
  refine ⟨2 + C₀ + Cₛ + 2, ⟨R.adapt (by intro x i d hp; exact hp) ?_ ?_ ?_⟩⟩
  · intro x i d _
    change (if decide (i.width = 0) then inputBitWrite false i d else inputBitResult i d) = _
    by_cases hW : i.width = 0
    · simp only [decide_eq_true hW, if_true, inputBitResult_width_zero i d hW]
    · simp only [decide_eq_false hW, Bool.false_eq_true, if_false]
  · intro x i
    change 2 * i.width + 2 + 1 + C₀ * (i.width + 1) +
      Cₛ * (i.width + x.length + 1) + 1 ≤ (2 + C₀ + Cₛ + 2) * (i.width + x.length + 1)
    have h := Nat.mul_le_mul_left C₀ (show i.width + 1 ≤ i.width + x.length + 1 by omega)
    simp only [Nat.add_mul]
    omega
  · intro x i
    change 2 * i.width + 2 + C₀ * (i.width + 1) +
      Cₛ * (i.width + (Nat.bits x.length).length + 1) ≤
        (2 + C₀ + Cₛ + 2) * (i.width + (Nat.bits x.length).length + 1)
    have h := Nat.mul_le_mul_left C₀
      (show i.width + 1 ≤ i.width + (Nat.bits x.length).length + 1 by omega)
    simp only [Nat.add_mul]
    omega

/-- The physical result has precisely the public row's framed endpoint shape. -/
private theorem inputBitResult_cfg {x : List Bool} {S : Type} (i : InputBitArgs)
    (d : InputBitData x) (entry exit : S) : (inputBitResult i d).cfg exit =
    { d.cfg entry with
      state := some exit
      inputPos := (inputBitResult i d).inputPos
      workTapes := wordWrite (d.cfg entry) 2 (bvBits
        (if 0 ≤ i.index.toInt ∧ x.getD i.index.toInt.toNat false = true then
          (1 : BitVec i.width) else 0)) } := by
  classical
  by_cases h : inputBitCanRead x i <;>
    apply Cfg.ext <;> (try funext j) <;> (try funext z) <;>
    simp only [inputBitResult, inputBitWrite, inputBitSeek, inputBitAnswer,
      h, if_true, if_false, InputBitData.cfg, wordWrite_apply, decide_eq_true_eq]

/-- **Reading an input bit at a word's position.** A five-tape machine over `Bool`. From the entry,
with a word `u` of `W` bits on tape `0`, the input length `Nat.bits |x|` on tape `1`, a register
word of `W` cells on tape `2` and blank scratch tapes (`Turing.ScratchBlank`), the input head
anywhere: the row writes on tape `2` the word `1` if `0 ≤ u.toInt` and the input bit at position
`u.toInt` is `true`, and the word `0` otherwise (positions past the input read `false`), and
stops at its exit within `C·(W + |x| + 1)` steps, every work head within `C·(W + log |x| + 1)`
cells and back where it started. The input head ends somewhere. [AB09, §4.1, Exercise 1.9]

**Proof sketch.** Use `inputBitFullCall`, built with `Contract.seq`, `Contract.branch` and
`Contract.inPhase`. First the catalog comparison with empty scratch handles width zero. The
sign row handles negative positions; `inputBitCompareTM` handles positions past the input.
For a valid position, copy and increment its positive-width word, apply the embedded native
seek, and clear the counter. `inputBitReadTM` selects the integer-constant writer for its bit.
The native seek keeps its width-only work envelope; every other call has linear time and
radius. `inputBitResult_cfg` identifies the resulting physical fields with the stated endpoint,
and its input position supplies the existential witness. -/
theorem exists_inputBitTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (Nat.bits x.length) →
        WordAt d 2 w → w.length = W → ScratchBlank d →
        ∃ ip : Fin (x.length + 2),
          ReachesWithin R d {some exit} (C * (W + x.length + 1))
            (C * (W + (Nat.bits x.length).length + 1))
            { d with state := some exit, inputPos := ip,
                     workTapes := wordWrite d 2 (bvBits
                       (if 0 ≤ u.toInt ∧ x.getD u.toInt.toNat false = true then (1 : BitVec W)
                        else 0)) } := by
  obtain ⟨C, ⟨R⟩⟩ := inputBitFullCall
  refine ⟨R.S, R.finite, R.decEq, R.M, R.entry, R.exit, C, ?_⟩
  intro x W u w d hd hu hn hw hlen hb
  let i : InputBitArgs := ⟨W, u, w⟩
  let data := InputBitData.ofCfg d
  have hp : inputBitReady i data := by
    refine ⟨?_, ?_, ?_, hlen, ?_⟩
    · rw [wordAt_iff] at hu ⊢; exact hu
    · rw [wordAt_iff] at hn ⊢; exact hn
    · rw [wordAt_iff] at hw ⊢; exact hw
    · rw [scratchBlank_iff] at hb ⊢; exact hb
  have hr := R.reaches i data hp
  have hc : data.cfg R.entry = d := InputBitData.cfg_ofCfg d R.entry hd
  rw [hc] at hr
  have he := inputBitResult_cfg i data R.entry R.exit
  rw [hc] at he
  refine ⟨(inputBitResult i data).inputPos, ?_⟩
  rw [← he]
  exact hr

end Turing
