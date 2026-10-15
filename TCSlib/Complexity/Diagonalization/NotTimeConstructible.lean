/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.Uncomputability.Halting
import Mathlib.Data.Nat.Digits.Lemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A function that is not time-constructible

[AB09, Exercise 3.5]: not every function is time-constructible. Stated
non-trivially: `Complexity.TimeConstructible` already packages the growth
condition `∀ n, n ≤ T n`, so a function violating that (`T = 0`, say) fails
for a vacuous reason; the statement below therefore demands a function
*dominating the identity* that still fails constructibility, pinning the
failure on the computability half — a constructibility witness for the
exhibited `T` would decide the halting problem.

## Design

* The witness oscillates between `n` and `n + 1` according to the halting
  function `Complexity.HALT` at the campaign's fixed effective scheme
  `Complexity.TimeHierarchy.code` (reused, not re-chosen), evaluated on the
  `n`-th binary string of the little-endian dyadic enumeration: a word is
  read least-significant bit first, behind a high sentinel `1` appended to
  the list. The definition is classical and noncomputable — legitimate, since it lives
  inside an existence proof.
* The refutation uses only the *computability* of a constructibility witness
  (a machine computing `(T |x|).bits` on every input), not its time bound:
  `Complexity.Computable` carries no clock, so even the exponentially long
  intermediate strings of the reduction are harmless.

## Main results (proved; phase-P3.2 statement)

* `Complexity.exists_not_timeConstructible` — some `T` with `∀ n, n ≤ T n` is
  not time-constructible. [AB09, Exercise 3.5]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Chapter 3, Exercise 3.5; §1.5.1,
  Theorem 1.11.)
-/

namespace Complexity

open Turing

/-! ### The dyadic enumeration and the witness (private) -/

/-- The dyadic rank of a binary string: `s` read little-endian behind a high `1`, minus
one. -/
private def ntcRank (s : List Bool) : ℕ := codeBitsNat (s ++ [true]) - 1

/-- The dyadic un-rank: drop the high `1` of `n + 1`. -/
private def ntcStr (n : ℕ) : List Bool := (n + 1).bits.dropLast

/-- The witness of the exercise: `n`, plus one exactly when the `n`-th string halts at the
campaign's effective scheme. -/
private noncomputable def ntcT (n : ℕ) : ℕ :=
  n + if HALT TimeHierarchy.code.toMachineCode (ntcStr n) = true then 1 else 0

/-- `Turing.codeBitsNat` is Mathlib's base-2 `Nat.ofDigits`.

**Proof sketch.** Induct on the word; each step is one `Nat.bit`. -/
private theorem ntc_codeBitsNat_eq_ofDigits (w : List Bool) :
    codeBitsNat w = Nat.ofDigits 2 (w.map fun b => cond b 1 0) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change Nat.bit b (codeBitsNat w) = _
    cases b
    · simp [Nat.bit, Nat.ofDigits_cons, ih]
    · simp [Nat.bit, Nat.ofDigits_cons, ih]; omega

/-- A word ending in `true` is the binary representation of its value.

**Proof sketch.** Mathlib's `Nat.digits_ofDigits` and `Nat.digits_two_eq_bits`, through
the previous lemma; no induction on bits. -/
private theorem ntc_bits_codeBitsNat_append_true (s : List Bool) :
    (codeBitsNat (s ++ [true])).bits = s ++ [true] := by
  have hd := Nat.digits_ofDigits 2 (by norm_num) ((s ++ [true]).map fun b => cond b 1 0)
    (by intro l hl; simp only [List.mem_map] at hl; obtain ⟨b, -, rfl⟩ := hl; cases b <;> simp)
    (by intro h; simp)
  rw [← ntc_codeBitsNat_eq_ofDigits, Nat.digits_two_eq_bits] at hd
  exact (List.map_injective_iff.2 fun a b h => by cases a <;> cases b <;> simp_all) hd

/-- `(rank s + 1).bits = s ++ [true]`.

**Proof sketch.** The value is positive, so the predecessor cancels. -/
private theorem ntc_bits_rank_succ (s : List Bool) : (ntcRank s + 1).bits = s ++ [true] := by
  have h := ntc_bits_codeBitsNat_append_true s
  have hpos : 0 < codeBitsNat (s ++ [true]) :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_bits] at h; simp at h
  unfold ntcRank
  rw [Nat.sub_add_cancel hpos]
  exact h

/-- Un-rank inverts rank (only this direction is needed).

**Proof sketch.** The previous lemma, then `List.dropLast_concat`. -/
private theorem ntc_str_rank (s : List Bool) : ntcStr (ntcRank s) = s := by
  unfold ntcStr
  rw [ntc_bits_rank_succ, List.dropLast_concat]

/-- The low bit of the witness is the low bit of `n`, exclusive-or the halting bit.

**Proof sketch.** Case on the halting bit. -/
private theorem ntc_bodd_T (n : ℕ) :
    (ntcT n).bodd = (n.bodd ^^ HALT TimeHierarchy.code.toMachineCode (ntcStr n)) := by
  unfold ntcT
  cases h : HALT TimeHierarchy.code.toMachineCode (ntcStr n) <;> simp

/-- The rank is primitive recursive.

**Proof sketch.** Append, read the value, take the predecessor. -/
private theorem ntc_primrec_rank : Primrec ntcRank :=
  (Primrec.pred.comp (codePrimBitsNat.comp
    (Primrec.list_concat.comp Primrec.id (Primrec.const true)))).of_eq fun s => by
      simp [ntcRank, Nat.pred_eq_sub_one]

/-- **Stages (i)–(ii)**, the rank emitter `s ↦ 1^(rank s)` as a mapped range: primitive
recursive. -/
private theorem ntc_primrec_emit :
    Primrec fun s : List Bool => (List.range (ntcRank s)).map fun _ => true :=
  Primrec.list_map (Primrec.list_range.comp ntc_primrec_rank) (Primrec.const true).to₂

/-- The rank's parity, `s ↦ [bodd (rank s)]`: primitive recursive. -/
private theorem ntc_primrec_parity : Primrec fun s : List Bool => [(ntcRank s).bodd] :=
  Primrec.list_cons.comp (Primrec.nat_bodd.comp ntc_primrec_rank) (Primrec.const [])

/-- The low-bit tail `w ↦ [w.headI]`: primitive recursive. -/
private theorem ntc_primrec_head : Primrec fun w : List Bool => [w.headI] :=
  Primrec.list_cons.comp Primrec.list_headI (Primrec.const [])

/-- The negated low-bit tail `w ↦ [!w.headI]`: primitive recursive. -/
private theorem ntc_primrec_nhead : Primrec fun w : List Bool => [!w.headI] :=
  Primrec.list_cons.comp (Primrec.not.comp Primrec.list_headI) (Primrec.const [])

/-- The witness is not time-constructible: a constructibility witness would decide
halting.

**Proof sketch.** Compile the emitter, the parity decider and the two tails with
`Turing.codePrim_machine`; compose emitter and witness machine, and each tail after them,
with `Turing.FinTM.exists_comp_partial`; branch on the rank's parity with
`Turing.FinTM.exists_cond`. The composite outputs the halting bit, against
`Complexity.HALT_not_computable`. -/
private theorem ntc_not_timeConstructible : ¬TimeConstructible ntcT := by
  classical
  rintro ⟨-, c₀, -, M, hM⟩
  let h := HALT TimeHierarchy.code.toMachineCode
  obtain ⟨E, _, hE⟩ := codePrim_machine _ ntc_primrec_emit
  obtain ⟨D, _, hD⟩ := codePrim_machine _ ntc_primrec_parity
  obtain ⟨H₀, _, hH₀⟩ := codePrim_machine _ ntc_primrec_head
  obtain ⟨H₁, _, hH₁⟩ := codePrim_machine _ ntc_primrec_nhead
  obtain ⟨EM, hEM⟩ := FinTM.exists_comp_partial E M
  obtain ⟨B₀, hB₀⟩ := FinTM.exists_comp_partial EM H₀
  obtain ⟨B₁, hB₁⟩ := FinTM.exists_comp_partial EM H₁
  -- the middle stage: `E ≫ M` halts on `s` exactly with `(T (rank s)).bits`
  have hmid (s : List Bool) : ∃ t, EM.ComputesInTime s (ntcT (ntcRank s)).bits t :=
    (hEM s _).2 ⟨_, ⟨_, hE s⟩, _, by simpa using hM ((List.range (ntcRank s)).map fun _ => true)⟩
  have hlow (s : List Bool) :
      (ntcT (ntcRank s)).bits.headI = ((ntcRank s).bodd ^^ h s) := by
    rw [← Nat.bodd_eq_bits_head, ntc_bodd_T, ntc_str_rank]
  obtain ⟨R, hR⟩ := FinTM.exists_cond D B₁ B₀ (fun s => (ntcRank s).bodd) hD.computes
  refine HALT_not_computable TimeHierarchy.code ⟨R, fun s => ?_⟩
  refine (hR s _).2 ?_
  cases hp : (ntcRank s).bodd with
  | false =>
    simp only [cond_false]
    have hc := hH₀ (ntcT (ntcRank s)).bits
    dsimp only at hc
    rw [hlow, hp, Bool.false_xor] at hc
    exact (hB₀ s _).2 ⟨_, hmid s, _, hc⟩
  | true =>
    simp only [cond_true]
    have hc := hH₁ (ntcT (ntcRank s)).bits
    dsimp only at hc
    rw [hlow, hp, Bool.true_xor, Bool.not_not] at hc
    exact (hB₁ s _).2 ⟨_, hmid s, _, hc⟩

/-- **Not every function is time-constructible** [AB09, Exercise 3.5]: there
is a function `T` dominating the identity (`∀ n, n ≤ T n` — so the failure is
not the vacuous growth-condition one, see the module docstring) that is not
time-constructible.

**Proof sketch.** Fix the campaign's effective scheme
`c := Complexity.TimeHierarchy.code` and the little-endian dyadic
enumeration `str : ℕ → List Bool` of binary strings — the rank of a string
`s` is the value of `s ++ [true]` read least-significant bit first (a high
sentinel `1` appended to the list), minus one, so rank and un-rank are both
bit-rewrites. Define, classically,

  `T n := n + (if HALT c.toMachineCode (str n) = true then 1 else 0)`.

Then `∀ n, n ≤ T n` by construction. Suppose `TimeConstructible T` held, with
witness machine `M` computing `(T |x|).bits` on every input `x` (the clock
`c₀ · (T n + 1)` of `Complexity.TimeConstructible` is not even needed — only
the witness's totality). Then `fun s => [HALT c.toMachineCode s]` would be
computable, contradicting `Complexity.HALT_not_computable c`: on input `s`,
(i) compute the rank word `(rank s).bits` (the dyadic bit-rewrite — the
string-of-index bridge obligation); (ii) emit a string of length `rank s`,
say `1^(rank s)`, by a binary-countdown unary emitter (the
`TimeHierarchy.ClockMachine`/`ClockLoop` counter precedent;
`Complexity.Computable` has no time bound, so the exponential length is
harmless); (iii) run `M` on it, producing `(T (rank s)).bits`; (iv) compare
that word against `(rank s).bits` (equality-test tail,
`Turing.FinTM.computesFunInTime_ifEq` precedent — for an even rank this is
[AB09]'s "read the low bit of `(T n).bits`", and the full equality test also
covers the odd-rank carry), outputting `[true]` exactly when the two differ,
i.e. when `T (rank s) = rank s + 1`, i.e. when `HALT c.toMachineCode s =
true`. Assemble the stages with `Turing.FinTM.exists_comp_partial`, collapsing
intermediate outputs by determinism (`Turing.FinTM.ComputesInTime.output_unique`),
exactly as in `Complexity.UC_computable_of_HALT_computable`. Fill obligations,
named for the brief: the rank machine and the unary emitter (i)-(ii); the
comparison tail (iv); the composition assembly; and the final classical case
split on `HALT` identifying the composite's output with the halting bit.

**Route as filled** (flagged appendix, B8 fill). Stages (i)–(ii) are combined in one
emitter `s ↦ 1^(rank s)`, read as a mapped range and compiled by the primitive-recursive
compiler `Turing.codePrim_machine`, with no hand-built counter. Stage (iii) runs the
constructor that `TimeConstructible T` assumes, composed with the emitter by
`Turing.FinTM.exists_comp_partial`; `T` itself is never compiled. Stage (iv) reads a bit
guaranteed to differ between the two candidates: the low bit of `(T (rank s)).bits`
exclusive-or the rank's parity (the parity decider and the two tails are compiled too),
branched with `Turing.FinTM.exists_cond`. That bit is the halting bit, so no
two-word comparator is needed. The bit identity `(rank s + 1).bits = s ++ [true]` comes
from Mathlib's `Nat.digits_ofDigits`, with no induction on bits. -/
theorem exists_not_timeConstructible :
    ∃ T : ℕ → ℕ, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T :=
  ⟨ntcT, fun _ => Nat.le_add_right _ _, ntc_not_timeConstructible⟩

end Complexity
