/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the input length in binary (§12.8, R8.5c)

The native-input row R8.5c of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3, §12.8b): count the native input into a
little-endian binary word on a dedicated work tape, `Nat.bits |x|`, in linear
time and logarithmic work space. It is a `Bool` module; a rich host runs it
lifted along its digit embedding (`Turing.MultiTapeTM.liftSymbols`), with
unchanged time and space. The record template and the initial record
(`Build/RecordTable.lean`) take their position width from it, and the
space-constructibility witnesses of chapter 4 count with it.

**Status: proved.** The framed input-length contract is proved by a single
input pass with a binary counter, followed by the public input rewind.

## Design

* **Own module** (§12.8b decision proposal W1-5): the natural home is beside
  `Turing.exists_inputSeekTM` in `Build/InputCall.lean`, which an in-flight fill
  batch owns. This module imports only `Build/CounterLoop`, so the
  constructibility files can import it without the record layer; 12.2c may fold
  it into `Build/InputCall.lean`.
* **Framed output.** The dedicated tape need only be blank on the interval the
  word and its two delimiters occupy, so the module also runs on a tape that
  carries unrelated data elsewhere.
* **Input position.** The module starts with the input head at `1` and returns it
  there, as `Turing.inputCopyTM` and `Turing.inputFoldTM` do.

## Main results

* `Turing.exists_inputLengthTM` — write `Nat.bits |x|` on a dedicated tape
  (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1: a machine counts its input
  length in binary with a work-tape counter in `O(log n)` space; p. 79, the
  space-constructibility of `log n`.)
-/

namespace Turing

/-- The six phases of the single-pass input counter. -/
private inductive InputLengthPhase where
  | count | carry | back | returnStart | returnScan | done
  deriving DecidableEq, Fintype

/-- The framed counter's only hand-built table: there is no public input-driven
counter. Carry and work-head rewind implement the counting phase of Catalog's
`f2_counterTM`; the native-input return uses the public input-fold transition
and rewind contract.

**Fill appendix.** The input-advance step is separate from the carry, costing
one extra step per round. A round with `p` cleared digits therefore costs
`2*p + 3`; its cost plus twice the change in the true-bit count is five.
The exit is stationary so the least exit time has the same exact finish. -/
private def inputLengthMachine : MultiTapeTM 1 Bool InputLengthPhase where
  q₀ := .count
  tr := fun phase inp work =>
    match phase with
    | .count =>
      match inp with
      | some _ => inputMoveAction .pos .carry
      | none => inputMoveAction 0 .returnStart
    | .carry =>
      if work 0 = some true then tapeAction 0 0 (some (some false)) .pos .carry
      else tapeAction 0 0 (some (some true)) .neg .back
    | .back =>
      match work 0 with
      | some _ => tapeAction 0 0 none .neg .back
      | none => tapeAction 0 0 none .pos .count
    | .returnStart => FinTM.controlAction .neg (some .returnScan)
    | .returnScan =>
      ((inputFoldTM 1 (fun (_ : Unit) (_ : Bool) => ()) ()).tr (.bwd ()) inp work).mapState
        (fun q => match q with | .done _ => .done | _ => .returnScan)
    | .done => inputMoveAction 0 .done

/-- Splitting the canonical digits at their first zero also gives the successor's
canonical digits. The second alternative is the width-extension case.

**Proof sketch.** Binary induction removes the low digit. A zero ends the carry;
a one adds one cleared digit to the induction hypothesis. -/
private theorem inputLength_digits (n : ℕ) :
    ∃ p : ℕ, ∃ v : List Bool,
      (n.bits = List.replicate p true ++ false :: v ∨
        n.bits = List.replicate p true ∧ v = []) ∧
      (n + 1).bits = List.replicate p false ++ true :: v := by
  induction n using Nat.binaryRec' with
  | zero => exact ⟨0, [], Or.inr ⟨by simp, rfl⟩, by simp⟩
  | bit b n h ih =>
    cases b with
    | false =>
      refine ⟨0, n.bits, Or.inl ?_, ?_⟩
      · simpa using Nat.bits_append_bit n false h
      · simpa only [Nat.bit_val, Bool.toNat_false, Nat.add_zero,
          List.replicate_zero, List.nil_append] using Nat.bit1_bits n
    | true =>
      obtain ⟨p, v, old, next⟩ := ih
      refine ⟨p + 1, v, ?_, ?_⟩
      · rw [Nat.bits_append_bit n true h, List.replicate_succ]
        rcases old with old | ⟨old, rfl⟩
        · exact Or.inl (by simp [old])
        · exact Or.inr ⟨by simp [old], rfl⟩
      · have he : Nat.bit true n + 1 = 2 * (n + 1) := by
          simp [Nat.bit_val]; omega
        rw [he, Nat.bit0_bits (n + 1) (by omega), next, List.replicate_succ]
        rfl


/-- The split gives the potential change and the maximal visited offset. -/
private theorem inputLength_charge (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v) :
    (n + 1).bits.count true + p = n.bits.count true + 1 ∧
      p < (n + 1).bits.length := by
  rw [next]
  rcases old with old | ⟨old, rfl⟩ <;> simp [old, List.count_append, List.count_replicate] <;> omega

/-- A counter trace configuration. Only a prefix of the replacement word has
been written; all cells outside that prefix retain their entry values. -/
private def inputLengthCfg {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (s : InputLengthPhase) (ip : Fin (x.length + 2))
    (z : ℤ) : Cfg 1 Bool InputLengthPhase x :=
  { state := some s
    inputPos := ip
    workTapes := fun _ a =>
      if d.workTapePos 0 ≤ a ∧ a < d.workTapePos 0 + (r : ℤ)
      then FinTM.bufferTape w (a - d.workTapePos 0)
      else d.workTapes 0 a
    workTapePos := fun _ => d.workTapePos 0 + z
    output := d.output }

/-- The unwritten prefix with zero head offset leaves the data fields alone. -/
private theorem inputLengthCfg_zero {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (s : InputLengthPhase) (ip : Fin (x.length + 2)) :
    inputLengthCfg d w 0 s ip 0 = {d with state := some s, inputPos := ip} := by
  apply Cfg.ext <;> simp only [inputLengthCfg, Nat.cast_zero, add_zero]
  · funext j a
    have : j = 0 := Subsingleton.elim _ _
    subst j
    split_ifs with h
    · omega
    · rfl
  · funext j
    exact congrArg d.workTapePos (Subsingleton.elim _ _)

/-- Writing the next prefix cell follows the public framed-write identity.

**Proof sketch.** The one-tape action supplies the configuration update;
`catalog_write_take` supplies the entire tape equality, including its frame. -/
private theorem inputLength_write {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (hr : r < w.length) (s s' : InputLengthPhase)
    (ip : Fin (x.length + 2)) (m : SignType)
    (htr : inputLengthMachine.tr s
      (inputLengthCfg d w r s ip r).inputSymbol
      (inputLengthCfg d w r s ip r).workTapeSymbols =
        tapeAction 0 0 (some (some w[r])) m s') :
    inputLengthMachine.step (inputLengthCfg d w r s ip r) =
      inputLengthCfg d w (r + 1) s' ip ((r : ℤ) + m) := by
  rw [step_of_tapeAction_write _ _ 0 0 (some w[r]) m rfl htr]
  apply Cfg.ext
  · rfl
  · simp only [inputLengthCfg, moveInputPos_zero]
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [Function.update_self, inputLengthCfg] using
      catalog_write_take (d.workTapes 0) (d.workTapePos 0) w r hr
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, inputLengthCfg]
    omega
  · rfl


/-- One input symbol drives one framed increment, including width extension.

**Proof sketch.** The forward configurations replace successive low bits by
zeros; the first non-true cell is replaced by one on the turn. The return
configurations keep this prefix and move over its zeros to the left delimiter.
The two direct inductions concern this cyclic table, whose return state starts
the next round. At every intermediate time the head is between minus one and
`p`, relative to the entry head. -/
private theorem inputLength_round {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (hs : d.state = some .count) (hip : d.inputPos.val = n + 1) (hn : n < x.length)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (htape : ∀ a : ℤ, -1 ≤ a → a ≤ (n.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = FinTM.bufferTape n.bits a) :
    inputLengthMachine.runFrom d (2 * p + 3) =
        inputLengthCfg d (n + 1).bits (p + 1) .count
          (moveInputPos d.inputPos .pos) 0 ∧
      ∀ u ≤ 2 * p + 3,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (p : ℤ) := by
  let w := (n + 1).bits
  let ip := moveInputPos d.inputPos .pos
  let F := fun r : ℕ => inputLengthCfg d w r .carry ip r
  let R := fun r : ℕ => inputLengthCfg d w (p + 1) .back ip ((r : ℤ) - 1)
  let D := inputLengthCfg d w (p + 1) .count ip 0
  have plen : p < w.length := (inputLength_charge n p v old next).2
  have oldlen : p ≤ n.bits.length := by
    rcases old with h | ⟨h, _⟩ <;> simp [h]
  have fzero : inputLengthMachine.step d = F 0 := by
    have hi : d.inputSymbol = some x[n] := inputSymbolInner n (by omega) hn
    rw [step_of_inputMoveAction _ _ .pos hs (q' := .carry) (by
      simp [inputLengthMachine, hi])]
    exact (inputLengthCfg_zero d w .carry ip).symm
  have forward (r : ℕ) (hr : r < p) : inputLengthMachine.step (F r) = F (r + 1) := by
    have read : (F r).workTapeSymbols 0 = some true := by
      have cell := htape r (by omega) (by omega)
      have bit : n.bits[r]? = some true := by
        rcases old with h | ⟨h, _⟩ <;>
          simp [h, List.getElem?_append, hr]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat] using
        cell.trans (by simpa using bit)
    have digit : w[r] = false := by
      simp [w, next, hr]
    simpa only [F, Nat.cast_add, Nat.cast_one, SignType.cast] using
      inputLength_write d w r (by omega) .carry .carry ip .pos (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have turn : inputLengthMachine.step (F p) = R p := by
    have read : (F p).workTapeSymbols 0 ≠ some true := by
      have cell := htape p (by omega) (by omega)
      have bit : n.bits[p]? ≠ some true := by
        rcases old with h | ⟨h, _⟩ <;> simp [h]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, cell] using bit
    have digit : w[p] = true := by simp [w, next]
    simpa only [F, R, SignType.cast, sub_eq_add_neg] using
      inputLength_write d w p plen .carry .back ip .neg (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have backward (r : ℕ) (hr : r < p) : inputLengthMachine.step (R (r + 1)) = R r := by
    have read : (R (r + 1)).workTapeSymbols 0 = some false := by
      have digit : w[r]? = some false := by
        simp [w, next, List.getElem?_append, hr]
      simp [R, inputLengthCfg, Cfg.workTapeSymbols, show (r : ℤ) < p + 1 by omega,
        FinTM.bufferTape_nat, digit]
    rw [step_of_tapeAction_move _ _ 0 0 .neg rfl (q' := .back) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, SignType.cast]
    omega
  have entry : inputLengthMachine.step (R 0) = D := by
    have read : (R 0).workTapeSymbols 0 = none := by
      have cell := htape (-1) (by omega) (by omega)
      simpa [R, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_left] using cell
    rw [step_of_tapeAction_move _ _ 0 0 .pos rfl (q' := .count) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, D, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp [SignType.cast]
  have step_run (a : Cfg 1 Bool InputLengthPhase x) (u : ℕ) :
      inputLengthMachine.runFrom a (u + 1) =
        inputLengthMachine.step (inputLengthMachine.runFrom a u) :=
    MultiTapeTM.runFrom_succ_eq_step'
  have reachesF : ∀ r ≤ p, inputLengthMachine.runFrom d (r + 1) = F r := by
    intro r
    induction r with
    | zero => intro _; exact fzero
    | succ r ih =>
      intro hr
      rw [step_run, ih (by omega), forward r (by omega)]
  have reachesR : ∀ r ≤ p, inputLengthMachine.runFrom d (p + 2 + r) = R (p - r) := by
    intro r
    induction r with
    | zero =>
      intro _
      simpa only [Nat.add_zero, Nat.sub_zero] using
        (show inputLengthMachine.runFrom d (p + 2) = R p by
          rw [show p + 2 = (p + 1) + 1 by omega, step_run,
            reachesF p le_rfl, turn])
    | succ r ih =>
      intro hr
      rw [show p + 2 + (r + 1) = (p + 2 + r) + 1 by omega,
        step_run, ih (by omega)]
      rw [show p - r = (p - (r + 1)) + 1 by omega, backward _ (by omega)]
  have finish : inputLengthMachine.runFrom d (2 * p + 3) = D := by
    rw [show 2 * p + 3 = (p + 2 + p) + 1 by omega,
      step_run, reachesR p le_rfl, Nat.sub_self, entry]
  refine ⟨finish, ?_⟩
  intro u hu
  by_cases hz : u = 0
  · subst u; simp
  by_cases hf : u ≤ p + 1
  · rw [show u = (u - 1) + 1 by omega, reachesF _ (by omega)]
    simp only [F, inputLengthCfg]
    constructor <;> omega
  by_cases hb : u ≤ 2 * p + 2
  · rw [show u = p + 2 + (u - (p + 2)) by omega, reachesR _ (by omega)]
    simp only [R, inputLengthCfg]
    constructor <;> omega
  · rw [show u = 2 * p + 3 by omega, finish]
    simp only [D, inputLengthCfg, add_zero]
    constructor <;> omega

/-- A completely written word agrees with its buffer throughout the originally
blank slot, including both delimiters. -/
private theorem inputLengthCfg_read {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (w : List Bool) (s : InputLengthPhase)
    (ip : Fin (x.length + 2)) (N : ℕ)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (N : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none)
    (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (N : ℤ)) :
    (inputLengthCfg d w w.length s ip 0).workTapes 0 (d.workTapePos 0 + a) =
      FinTM.bufferTape w a := by
  simp only [inputLengthCfg, add_sub_cancel_left]
  split_ifs with h
  · rfl
  · rw [blank a ha hb]
    by_cases hn : 0 ≤ a
    · have hw' : w.length ≤ a.toNat := by omega
      simp [FinTM.bufferTape, hn, List.getElem?_eq_none hw']
    · simp [FinTM.bufferTape, hn]

/-- Consecutive canonical counter words differ only in the overwritten carry
prefix; overwriting that prefix therefore composes the two exterior frames.

**Proof sketch.** Below the origin nothing is touched. Inside the new prefix
the two sides read the new word. Above it the old and new words have the same
suffix, and their upper boundaries agree there, even on width extension. -/
private theorem inputLengthCfg_merge {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (ip ip' : Fin (x.length + 2)) :
    inputLengthCfg (inputLengthCfg d n.bits n.bits.length .count ip 0)
        (n + 1).bits (p + 1) .count ip' 0 =
      inputLengthCfg d (n + 1).bits (n + 1).bits.length .count ip' 0 := by
  have plen : p < (n + 1).bits.length := (inputLength_charge n p v old next).2
  apply Cfg.ext <;> simp only [inputLengthCfg, add_zero]
  funext j a
  by_cases hlow : d.workTapePos 0 ≤ a
  · by_cases hpre : a < d.workTapePos 0 + ((p + 1 : ℕ) : ℤ)
    · have hnew : a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by omega
      simp only [hlow, hpre, hnew, and_self, ite_true]
    · have offset : p + 1 ≤ (a - d.workTapePos 0).toNat := by omega
      have sameEnd : a < d.workTapePos 0 + (n.bits.length : ℤ) ↔
          a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by
        rcases old with h | ⟨h, hv⟩
        · simp [h, next]
        · simp [h, next, hv]; omega
      have suffix : FinTM.bufferTape n.bits (a - d.workTapePos 0) =
          FinTM.bufferTape (n + 1).bits (a - d.workTapePos 0) := by
        simp only [FinTM.bufferTape, if_pos (by omega : 0 ≤ a - d.workTapePos 0)]
        rcases old with h | ⟨h, hv⟩
        · simp only [h, next, List.getElem?_append,
            List.length_replicate, if_neg (by omega : ¬(a - d.workTapePos 0).toNat < p)]
          rw [List.getElem?_cons, List.getElem?_cons]
          simp [show (a - d.workTapePos 0).toNat - p ≠ 0 by omega]
        · simp [h, next, hv, List.getElem?_eq_none, offset]; omega
      simp only [hlow, hpre, true_and, ite_false, sameEnd, suffix]
  · simp only [hlow, false_and, ite_false]

/-- Counting the first `n` input symbols preserves the exterior frame and pays
exactly five units per symbol after including twice the true-bit potential.

**Proof sketch.** Induct on the number of symbols. The framed round theorem
provides each physical segment, the digit split identifies its next canonical
word, and the frame-composition lemma joins it to the original configuration.
The potential equation telescopes, while both segments' head intervals fit the
new binary width. -/
private theorem inputLength_count {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (hs : d.state = some .count)
    (hip : d.inputPos = 1)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (x.length.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none) :
    ∀ n (hn : n ≤ x.length), ∃ t,
      t + 2 * n.bits.count true = 5 * n ∧
      inputLengthMachine.runFrom d t =
        inputLengthCfg d n.bits n.bits.length .count ⟨n + 1, by omega⟩ 0 ∧
      ∀ u ≤ t,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (n.bits.length : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_zero]
      simp only [Nat.zero_bits, List.length_nil, inputLengthCfg_zero]
      apply Cfg.ext <;> simp [hs, hip]
    · intro u hu
      have : u = 0 := by omega
      subst u
      simp
  | succ n ih =>
    intro hn
    obtain ⟨t, charge, reached, bounded⟩ := ih (by omega)
    obtain ⟨p, v, old, next⟩ := inputLength_digits n
    have accounting := inputLength_charge n p v old next
    let ip : Fin (x.length + 2) := ⟨n + 1, by omega⟩
    let c := inputLengthCfg d n.bits n.bits.length .count ip 0
    have oldwidth : n.bits.length ≤ x.length.bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (show n ≤ x.length by omega)
    have newwidth : n.bits.length ≤ (n + 1).bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_succ n)
    have field (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (n.bits.length : ℤ)) :
        c.workTapes 0 (c.workTapePos 0 + a) = FinTM.bufferTape n.bits a := by
      simpa only [c, inputLengthCfg, add_zero] using
        inputLengthCfg_read d n.bits .count ip x.length.bits.length blank a ha (by omega)
    have round := inputLength_round c n p v rfl rfl (by omega) old next field
    have inext : moveInputPos c.inputPos .pos = (⟨n + 1 + 1, by omega⟩ : Fin (x.length + 2)) := by
      rw [moveInputPos_pos_of_ne_right _ (by simp only [c, inputLengthCfg, ip]; omega)]
      rfl
    have ctime : inputLengthMachine.runFrom d t = c := reached
    refine ⟨t + (2 * p + 3), by omega, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, ctime, round.1, inext]
      exact inputLengthCfg_merge d n p v old next ip _
    · intro u hu
      by_cases before : u ≤ t
      · obtain ⟨lower, upper⟩ := bounded u before
        exact ⟨lower, by omega⟩
      · have localBound := round.2 (u - t) (by omega)
        rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, ctime]
        have hcpos : c.workTapePos 0 = d.workTapePos 0 := by simp [c, inputLengthCfg]
        rw [hcpos] at localBound
        exact ⟨localBound.1, by omega⟩

/-- **R8.5c, the input length** (design §12.8a §3, §12.8b). There is a `Bool`
module with an entry and an exit state and `K + 1` tapes with the following
contract. Start it at its entry with the input head at position `1`, tape `0`
blank on the `|bits |x|| + 2` cells from one left of its head to one right of
where the word will end, and the other tapes blank. It reaches its exit within
`C·(|x| + 1)` steps, and not earlier. At that point tape `0` holds
`Nat.bits |x|` from its head, and every other cell, every head, the input
position and the output are as they were. Up to the exit every work head stays
within `C·(|bits |x|| + 1)` cells of its entry position, so the work space is
logarithmic in `|x|` however far the input head travels. At `x = []` nothing is
written, since `Nat.bits 0 = []`.

**Proof sketch.** One pass over the input drives an in-place binary counter on
tape `0`. For each input symbol, move the input head right and increment the
counter: the carry turns the maximal `true` prefix to `false` and writes `true`
on the next cell, which is the blank just after the word when the counter
overflows, so the width grows by one cell exactly at the powers of two. A
return pass brings the counter head back to its first cell, guided by the
blank delimiter on its left. At the input's right end marker, walk the input
head back to position `1` (the `Turing.inputFoldTM_run_ofCfg` return) and exit.
The increments from `0` to `|x|` cost `Σ_v (2·p_v + 2)` for the true-prefix
lengths `p_v`, which telescopes against twice the number of `true` cells, as
in `Turing.counterOverhead_le_of_le` mirrored, so the total is linear in
`|x|`. Route: the counting phase is the transition table of Catalog's private
`f2_counterTM` without its emission, framed; no public input-driven loop host
exists (`Turing.counterLoopTM` needs its round count on a tape, which is what
is being computed), so the fill proves the framed round induction for this
table directly and records the pair with `f2_counterTM` for 12.2c, which can
re-derive `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` from this row.
The counter head stays in `[pos - 1, pos + |bits |x||]`. -/
theorem exists_inputLengthTM :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM (K + 1) Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} (d : Cfg (K + 1) Bool S x), d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((Nat.bits x.length).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((Nat.bits x.length).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + ((Nat.bits x.length).length : ℤ)
                  then FinTM.bufferTape (Nat.bits x.length) (q - d.workTapePos j)
                else d.workTapes j q } := by
  refine ⟨0, InputLengthPhase, inferInstance, inferInstance, inputLengthMachine,
    .count, .done, 6, ?_⟩
  intro x d hs hip blank _
  obtain ⟨t, charge, counted, countHeads⟩ := inputLength_count d hs hip blank x.length le_rfl
  let c := inputLengthCfg d x.length.bits x.length.bits.length .count
    (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0
  let back : Cfg 1 Bool InputLengthPhase x := {c with state := some .returnStart}
  have endSymbol : c.inputSymbol = none := by
    simp [c, inputLengthCfg, Cfg.inputSymbol]
  have turn : inputLengthMachine.step c = back := by
    rw [step_of_inputMoveAction _ _ 0 rfl (q' := .returnStart) (by
      simp [inputLengthMachine, endSymbol])]
    simp only [moveInputPos_zero]
    rfl
  obtain ⟨r, hr, returned, returnHeads⟩ := FinTM.rewind_heads inputLengthMachine
    .returnStart .returnScan (some .done) (by intros; rfl)
    (by intro inp work; cases inp <;> rfl) back rfl
  have reachedBack : inputLengthMachine.runFrom d (t + 1) = back := by
    rw [MultiTapeTM.runFrom_succ_eq_step', counted]
    exact turn
  have finish : inputLengthMachine.runFrom d (t + 1 + r) =
      {back with state := some .done, inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, reachedBack, returned]
  have deadline : t + 1 + r ≤ 6 * (x.length + 1) := by
    have hr' : r ≤ x.length + 3 := by simpa [back, c, inputLengthCfg] using hr
    omega
  have heads (u : ℕ) (hu : u ≤ t + 1 + r) :
      d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
      (inputLengthMachine.runFrom d u).workTapePos 0 ≤
        d.workTapePos 0 + (x.length.bits.length : ℤ) := by
    by_cases h : u ≤ t
    · exact countHeads u h
    · have hu' : u - (t + 1) ≤ r := by omega
      rw [show u = t + 1 + (u - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, reachedBack, returnHeads _ hu']
      simp only [back, c, inputLengthCfg, add_zero]
      constructor <;> omega
  -- Select the first exit, and use stationarity to keep the exact finish.
  have exits : ∃ u, (inputLengthMachine.runFrom d u).state = some .done :=
    ⟨t + 1 + r, congrArg Cfg.state finish⟩
  let first := Nat.find exits
  have firstState : (inputLengthMachine.runFrom d first).state = some .done :=
    Nat.find_spec exits
  have firstLe : first ≤ t + 1 + r := Nat.find_min' exits (congrArg Cfg.state finish)
  have fixed : inputLengthMachine.step (inputLengthMachine.runFrom d first) =
      inputLengthMachine.runFrom d first := by
    rw [step_of_inputMoveAction _ _ 0 firstState (q' := .done) rfl]
    simp only [moveInputPos_zero]
    apply Cfg.ext <;> simp [firstState]
  have same : inputLengthMachine.runFrom d (t + 1 + r) =
      inputLengthMachine.runFrom d first := by
    rw [show t + 1 + r = first + (t + 1 + r - first) by omega,
      MultiTapeTM.runFrom_add]
    exact Function.iterate_fixed fixed _
  refine ⟨first, firstLe.trans deadline, ?_, ?_, ?_⟩
  · intro u hu
    exact Nat.find_min exits hu
  · intro u hu j
    have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
    subst j
    obtain ⟨lower, upper⟩ := heads u (hu.trans firstLe)
    apply abs_le.mpr
    push_cast
    constructor <;> omega
  · rw [← same, finish]
    apply Cfg.ext
    · rfl
    · exact hip.symm
    · funext j a
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · funext j
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · rfl

end Turing
