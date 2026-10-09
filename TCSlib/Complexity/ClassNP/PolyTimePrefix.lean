/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.CounterProgPolyTime
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.TuringMachine.CounterProgInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time prefix operations

The second component of a self-delimiting pair can be truncated, or have its
prefix removed, at the length of the first component. A one-register counter
program counts the doubled first component, then copies or skips that many
symbols of the second component. Malformed pairs produce the empty string.

## Main definitions

* `Complexity.PrefixByLength.take` and `drop` — total prefix operations on pairs.

## Main results

* `Complexity.polyTimeComputable_takePrefixByLength` and
  `polyTimeComputable_dropPrefixByLength` — both operations are polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3: splitting random strings in the
  proof of Theorem 7.8; §7.4.1: repeated trials.)
-/

namespace Complexity

namespace PrefixByLength

open Turing CounterProg

/-- Take a prefix of the second component of a pair as long as its first component;
malformed inputs return the empty string. -/
def take (z : List Bool) : List Bool :=
  (pairSndD z).take (pairFstD z).length

/-- Drop a prefix of the second component of a pair as long as its first component;
malformed inputs return the empty string. -/
def drop (z : List Bool) : List Bool :=
  (pairSndD z).drop (pairFstD z).length

/-- Control states of the shared prefix-copying program. -/
private inductive Label where
  | scan | secondFalse | secondTrue | bump | head | read | dec
  | emit (b : Bool) | copy | copyEmit (b : Bool) | stop
  deriving DecidableEq, Fintype

/-- One register stores the remaining number of prefix symbols. -/
private def regs (n : ℕ) : Fin 1 → ℕ := fun _ => n

/-- The program parses aligned doubled bits before the separator. In take mode
it copies until the counter reaches zero; in drop mode it skips that prefix,
then copies everything remaining. -/
private def program (keep : Bool) : Label → Instr 1 Label
  | .scan => .rd .stop .secondFalse .secondTrue
  | .secondFalse => .rd .stop .bump .head
  | .secondTrue => .rd .stop .stop .bump
  | .bump => .inc 0 .scan
  | .head => .jz 0 (if keep then .stop else .copy) .read
  | .read => if keep then .rd .stop (.emit false) (.emit true)
      else .rd .stop .dec .dec
  | .dec => .dec 0 .head
  | .emit b => .out b .dec
  | .copy => .rd .stop (.copyEmit false) (.copyEmit true)
  | .copyEmit b => .out b .copy
  | .stop => .halt

/-- Updating the only register replaces its constant value. -/
private theorem update_regs (n m : ℕ) :
    Function.update (regs n) (0 : Fin 1) m = regs m := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst hi
  simp [regs]

/-- The final copying phase prints the unread suffix in two steps per bit.
**Proof sketch.** Each read selects an output instruction and returns to the
copying state. At the end, one read and one halt finish the computation. -/
private theorem goes_copy (keep : Bool) (n : ℕ) (r : List Bool) :
    Goes (program keep) r .copy (regs n) 0 none (regs n) r.length r
      (2 * r.length + 2) := by
  induction r with
  | nil =>
    have hread : Goes (program keep) [] .copy (regs n) 0
        (some .stop) (regs n) 0 [] 1 :=
      goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [] .stop (regs n) 0 none (regs n) 0 [] 1 :=
      goes_halt rfl
    simpa using hread.trans hhalt
  | cons b r ih =>
    have hread : Goes (program keep) (b :: r) .copy (regs n) 0
        (some (.copyEmit b)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hwrite : Goes (program keep) (b :: r) (.copyEmit b) (regs n) 1
        (some .copy) (regs n) 1 [b] 1 :=
      goes_out rfl
    have hrest := ih.prepend_input [b]
    have h := (hread.trans hwrite).trans hrest
    exact h.congr rfl rfl rfl (by simp; omega) (by simp) (by simp; omega)

/-- The countdown instruction removes one from the only register. -/
private theorem goes_dec_one (keep : Bool) (x : List Bool) (n p : ℕ) :
    Goes (program keep) x .dec (regs (n + 1)) p (some .head) (regs n) p [] 1 := by
  have h : Goes (program keep) x .dec (regs (n + 1)) p (some .head)
      (Function.update (regs (n + 1)) 0 ((regs (n + 1)) 0 - 1)) p [] 1 :=
    goes_dec rfl
  have he : (regs (n + 1)) (0 : Fin 1) - 1 = n := by simp [regs]
  rw [he, update_regs] at h
  exact h

/-- Starting with a counter of value `n`, the payload phase produces the
requested prefix or suffix in a linear number of steps.
**Proof sketch.** Induct on the payload. A positive counter consumes one bit
and decrements. A zero counter either halts immediately (take mode), or
enters the copying phase (drop mode). End-of-input halts in either mode. -/
private theorem goes_payload (keep : Bool) (r : List Bool) (n : ℕ) :
    Goes (program keep) r .head (regs n) 0 none (regs (n - r.length))
      (if keep then min n r.length else r.length)
      (if keep then r.take n else r.drop n) (4 * r.length + 3) := by
  induction r generalizing n with
  | nil =>
    cases n with
    | zero =>
      cases keep
      · have htest : Goes (program false) [] .head (regs 0) 0
            (some .copy) (regs 0) 0 [] 1 :=
          goes_jz_zero rfl rfl
        simpa using htest.trans (goes_copy false 0 [])
      · have htest : Goes (program true) [] .head (regs 0) 0
            (some .stop) (regs 0) 0 [] 1 :=
          goes_jz_zero rfl rfl
        have hhalt : Goes (program true) [] .stop (regs 0) 0
            none (regs 0) 0 [] 1 := goes_halt rfl
        exact (htest.trans hhalt).congr rfl rfl rfl (by simp) (by simp) (by simp)
    | succ n =>
      have htest : Goes (program keep) [] .head (regs (n + 1)) 0
          (some .read) (regs (n + 1)) 0 [] 1 :=
        goes_jz_pos rfl (by simp [regs])
      have hread : Goes (program keep) [] .read (regs (n + 1)) 0
          (some .stop) (regs (n + 1)) 0 [] 1 := by
        cases keep <;> exact goes_rd_end rfl (by simp)
      have hhalt : Goes (program keep) [] .stop (regs (n + 1)) 0
          none (regs (n + 1)) 0 [] 1 := goes_halt rfl
      exact ((htest.trans hread).trans hhalt).congr rfl (by simp) rfl
        (by cases keep <;> simp) (by cases keep <;> simp) (by simp)
  | cons b r ih =>
    cases n with
    | zero =>
      cases keep
      · have htest : Goes (program false) (b :: r) .head (regs 0) 0
            (some .copy) (regs 0) 0 [] 1 := goes_jz_zero rfl rfl
        exact (htest.trans (goes_copy false 0 (b :: r))).congr rfl (by simp) rfl
          (by simp) (by simp) (by simp; omega)
      · have htest : Goes (program true) (b :: r) .head (regs 0) 0
            (some .stop) (regs 0) 0 [] 1 := goes_jz_zero rfl rfl
        have hhalt : Goes (program true) (b :: r) .stop (regs 0) 0
            none (regs 0) 0 [] 1 := goes_halt rfl
        exact (htest.trans hhalt).congr rfl (by simp) rfl (by simp) (by simp)
          (by simp; omega)
    | succ n =>
      have htest : Goes (program keep) (b :: r) .head (regs (n + 1)) 0
          (some .read) (regs (n + 1)) 0 [] 1 :=
        goes_jz_pos rfl (by simp [regs])
      have hbody : Goes (program keep) (b :: r) .read (regs (n + 1)) 0
          (some .head) (regs n) 1 (if keep then [b] else []) 3 := by
        cases keep
        · have hread : Goes (program false) (b :: r) .read (regs (n + 1)) 0
              (some .dec) (regs (n + 1)) 1 [] 1 := by
            cases b
            · exact goes_rd_false rfl (by simp)
            · exact goes_rd_true rfl (by simp)
          exact (hread.trans (goes_dec_one false (b :: r) n 1)).congr
            rfl rfl rfl rfl (by simp) (by omega)
        · have hread : Goes (program true) (b :: r) .read (regs (n + 1)) 0
              (some (.emit b)) (regs (n + 1)) 1 [] 1 := by
            cases b
            · exact goes_rd_false rfl (by simp)
            · exact goes_rd_true rfl (by simp)
          have hwrite : Goes (program true) (b :: r) (.emit b) (regs (n + 1)) 1
              (some .dec) (regs (n + 1)) 1 [b] 1 := goes_out rfl
          simpa using (hread.trans hwrite).trans (goes_dec_one true (b :: r) n 1)
      have hrest := (ih n).prepend_input [b]
      exact ((htest.trans hbody).trans hrest).congr rfl (by simp) rfl
        (by cases keep <;> simp <;> omega)
        (by cases keep <;> simp)
        (by simp; omega)

/-- Each doubled source bit increments the length counter once. -/
private theorem goes_inc_one (keep : Bool) (x : List Bool) (n p : ℕ) :
    Goes (program keep) x .bump (regs n) p (some .scan) (regs (n + 1)) p [] 1 := by
  have h : Goes (program keep) x .bump (regs n) p (some .scan)
      (Function.update (regs n) 0 ((regs n) 0 + 1)) p [] 1 := goes_inc rfl
  have he : (regs n) (0 : Fin 1) + 1 = n + 1 := rfl
  rw [he, update_regs] at h
  exact h

/-- Parsing a doubled prefix adds its length to the counter and prints nothing.
**Proof sketch.** Induct on the prefix. Two reads recognize each equal bit
pair, then one increment returns to the scanning state. The remainder of
the run is transported past the two consumed input bits. -/
private theorem goes_doubled (keep : Bool) (u tail : List Bool) (n : ℕ) :
    Goes (program keep) (dbl u ++ tail) .scan (regs n) 0 (some .scan)
      (regs (n + u.length)) (2 * u.length) [] (3 * u.length) := by
  induction u generalizing n with
  | nil =>
    simp only [dbl_nil, List.nil_append, List.length_nil, Nat.add_zero, Nat.mul_zero]
    intro o
    exact ⟨0, le_rfl, by simp [run_zero]⟩
  | cons b u ih =>
    have hfirst : Goes (program keep) (dbl (b :: u) ++ tail) .scan (regs n) 0
        (some (if b then .secondTrue else .secondFalse)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) (dbl (b :: u) ++ tail)
        (if b then .secondTrue else .secondFalse) (regs n) 1
        (some .bump) (regs n) 2 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hinc := goes_inc_one keep (dbl (b :: u) ++ tail) n 2
    have hrest := (ih (n + 1)).prepend_input [b, b]
    have h := ((hfirst.trans hsecond).trans hinc).trans hrest
    exact h.congr rfl (by congr 1; simp; omega) rfl (by simp; omega)
      (by simp) (by simp; omega)

/-- On a well-formed pair the complete program computes the desired prefix
operation with at most `5(|z|+1)` abstract steps.
**Proof sketch.** Parse the doubled first component, consume the separator,
then run the payload phase with the counted length. The three linear time
bounds add to a linear bound in the encoded input length. -/
private theorem goes_pair (keep : Bool) (u r : List Bool) :
    ∃ (ρ : Fin 1 → ℕ) (p : ℕ), Goes (program keep) (pairEncode u r) .scan (regs 0) 0
      none ρ p (if keep then r.take u.length else r.drop u.length)
      (5 * ((pairEncode u r).length + 1)) := by
  have hfirst : Goes (program keep) ([false, true] ++ r) .scan (regs u.length) 0
      (some .secondFalse) (regs u.length) 1 [] 1 :=
    goes_rd_false rfl (by simp)
  have hsecond : Goes (program keep) ([false, true] ++ r) .secondFalse
      (regs u.length) 1 (some .head) (regs u.length) 2 [] 1 :=
    goes_rd_true rfl (by simp)
  have hhead := (goes_payload keep r u.length).prepend_input [false, true]
  have hsep := (hfirst.trans hsecond).trans hhead
  have hprefix : Goes (program keep) (dbl u ++ ([false, true] ++ r)) .scan (regs 0) 0
      (some .scan) (regs u.length) (2 * u.length) [] (3 * u.length) := by
    simpa using goes_doubled keep u ([false, true] ++ r) 0
  have hshift : Goes (program keep) (dbl u ++ ([false, true] ++ r)) .scan
      (regs u.length) (2 * u.length) none (regs (u.length - r.length))
      (2 * u.length + 2 + (if keep then min u.length r.length else r.length))
      (if keep then r.take u.length else r.drop u.length) (4 * r.length + 5) := by
    exact (hsep.prepend_input (dbl u)).congr rfl rfl (by simp)
      (by simp; omega) (by simp) (by omega)
  have hrun := hprefix.trans hshift
  have he : dbl u ++ ([false, true] ++ r) = pairEncode u r := by
    simp [pairEncode_eq_dbl, List.append_assoc]
  rw [he] at hrun
  refine ⟨regs (u.length - r.length),
    2 * u.length + 2 + (if keep then min u.length r.length else r.length), ?_⟩
  exact hrun.congr rfl rfl rfl rfl (by simp) (by simp [length_pairEncode]; omega)

/-- An incomplete or forbidden aligned pair halts without printing.
**Proof sketch.** The only invalid tails are an empty word, one bit, or a
tail starting with `10`. At most two reads reach the halt instruction. -/
private theorem goes_bad_tail (keep : Bool) (tail : List Bool) (n : ℕ)
    (htail : tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) :
    ∃ p : ℕ, Goes (program keep) tail .scan (regs n) 0 none (regs n) p [] 3 := by
  rcases htail with rfl | ⟨b, rfl⟩ | ⟨r, rfl⟩
  · have hread : Goes (program keep) [] .scan (regs n) 0
        (some .stop) (regs n) 0 [] 1 := goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [] .stop (regs n) 0
        none (regs n) 0 [] 1 := goes_halt rfl
    exact ⟨0, (hread.trans hhalt).congr rfl rfl rfl rfl (by simp) (by omega)⟩
  · have hfirst : Goes (program keep) [b] .scan (regs n) 0
        (some (if b then .secondTrue else .secondFalse)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) [b]
        (if b then .secondTrue else .secondFalse) (regs n) 1
        (some .stop) (regs n) 1 [] 1 := by
      cases b <;> exact goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [b] .stop (regs n) 1
        none (regs n) 1 [] 1 := goes_halt rfl
    exact ⟨1, by simpa using (hfirst.trans hsecond).trans hhalt⟩
  · have hfirst : Goes (program keep) (true :: false :: r) .scan (regs n) 0
        (some .secondTrue) (regs n) 1 [] 1 := goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) (true :: false :: r) .secondTrue (regs n) 1
        (some .stop) (regs n) 2 [] 1 := goes_rd_false rfl (by simp)
    have hhalt : Goes (program keep) (true :: false :: r) .stop (regs n) 2
        none (regs n) 2 [] 1 := goes_halt rfl
    exact ⟨2, by simpa using (hfirst.trans hsecond).trans hhalt⟩

/-- The complete program computes the total prefix operation on every input.
**Proof sketch.** A decoded pair is handled by `goes_pair`. If decoding
fails, the input consists of a doubled prefix followed by an invalid tail;
parse that prefix and apply `goes_bad_tail`. Neither phase prints anything,
agreeing with the empty total projections of a malformed pair. -/
private theorem goes_total (keep : Bool) (z : List Bool) :
    ∃ (ρ : Fin 1 → ℕ) (p : ℕ), Goes (program keep) z .scan (regs 0) 0
      none ρ p (if keep then take z else drop z) (5 * (z.length + 1)) := by
  cases hz : pairDecode z with
  | some ab =>
    obtain ⟨u, r⟩ := ab
    have he := eq_pairEncode_of_pairDecode z u r hz
    subst z
    simpa [take, drop] using goes_pair keep u r
  | none =>
    obtain ⟨u, tail, he, htail⟩ := pairDecode_eq_none z hz
    subst z
    have hprefix : Goes (program keep) (dbl u ++ tail) .scan (regs 0) 0
        (some .scan) (regs u.length) (2 * u.length) [] (3 * u.length) := by
      simpa using goes_doubled keep u tail 0
    obtain ⟨p, hbad⟩ := goes_bad_tail keep tail u.length htail
    have hshift : Goes (program keep) (dbl u ++ tail) .scan (regs u.length)
        (2 * u.length) none (regs u.length) (2 * u.length + p) [] 3 := by
      simpa using hbad.prepend_input (dbl u)
    have hrun := hprefix.trans hshift
    refine ⟨regs u.length, 2 * u.length + p, ?_⟩
    exact hrun.congr rfl rfl rfl rfl
      (by cases keep <;> simp [take, drop, pairFstD, pairSndD, hz])
      (by simp; omega)

end PrefixByLength

/-- Taking from the second component of a pair a prefix as long as its first
component is polynomial-time computable. Malformed inputs return `[]`.
**Proof sketch.** Compile the one-register prefix program. Its abstract run
takes at most `5(|z|+1)` steps; counter-program simulation has polynomial
overhead. This implements the splitting operation used in [AB09, §7.3,
Theorem 7.8]. -/
theorem polyTimeComputable_takePrefixByLength :
    PolyTimeComputable PrefixByLength.take := by
  apply CounterProg.polyTimeComputable_of_goes
    (PrefixByLength.program true) PrefixByLength.Label.scan PrefixByLength.take 5 1
  intro z
  simpa only [Bool.true_eq_true, if_true, Nat.pow_one] using
    PrefixByLength.goes_total true z

/-- Dropping from the second component of a pair a prefix as long as its first
component is polynomial-time computable. Malformed inputs return `[]`.
**Proof sketch.** Use the same program in drop mode: skip the counted
prefix, then copy the remaining input. Its abstract time bound is still
`5(|z|+1)`, so compilation gives a polynomial-time machine. This is the
other splitting operation used in [AB09, §7.3, Theorem 7.8]. -/
theorem polyTimeComputable_dropPrefixByLength :
    PolyTimeComputable PrefixByLength.drop := by
  apply CounterProg.polyTimeComputable_of_goes
    (PrefixByLength.program false) PrefixByLength.Label.scan PrefixByLength.drop 5 1
  intro z
  simpa only [Bool.false_eq_true, if_false, Nat.pow_one] using
    PrefixByLength.goes_total false z

end Complexity
