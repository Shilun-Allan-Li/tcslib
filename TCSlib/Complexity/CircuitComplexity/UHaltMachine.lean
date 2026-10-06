/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.Uncomputability.Halting
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `UHALT` in the machine model, and `P ⊊ P/poly`

[AB09, §6.1.1, p.110]: "The inclusion `P ⊆ P/poly` is proper. For instance, there are
unary languages that are undecidable and hence are not in `P` (or for that matter in
`EXP`), whereas every unary language is in `P/poly`", witnessed by

  `UHALT = {1ⁿ : n's binary expansion encodes a pair ⟨M, x⟩ such that M halts on input x}`.

`TCSlib.Complexity.CircuitComplexity.UHalt` states this with Mathlib's `Nat.Partrec.Code`
and `ComputablePred`, which says nothing about the machines `Complexity.P` and
`Complexity.EXP` are built from. This file restates `UHALT` over this development's own
halting function `Complexity.HALT` [AB09, §1.5.1], proves that no finite binary machine
decides it within any time bound, and draws the book's conclusions.

## Main definitions

* `Complexity.binaryExpansion` — the binary expansion of `n`, most significant bit first.
* `Complexity.numOfString` — the number whose binary expansion is `1s`.
* `Complexity.UHALT` — [AB09, p.110], over a representation scheme.

## Main results

* `Complexity.HALT_computable_of_decidesInTime_UHALT` — the reduction `HALT ≤ UHALT`.
* `Complexity.not_decidesInTime_UHALT` — no machine decides `UHALT`, with any time bound.
* `Complexity.UHALT_not_mem_EXP`, `Complexity.UHALT_not_mem_P` — [AB09, p.110].
* `Complexity.UHALT_mem_PPoly` — `UHALT ∈ P/poly` [AB09, p.110 with Claim 6.8].
* `Complexity.exists_mem_PPoly_not_mem_EXP` — some language in `P/poly` is not in `EXP`.
* `Complexity.P_ssubset_PPoly_of_subset` — `P ⊆ P/poly` (Thm 6.6) implies `P ⊊ P/poly`.

## Divergences from [AB09, p.110]

* **Numbering.** The book leaves implicit how `n`'s binary expansion "encodes" a string.
  A binary expansion always starts with `1` (and `0` has none), so we read `n` as the string
  `s` with `binaryExpansion n = true :: s` — the standard bijection between the positive
  integers and `{0,1}*`. `n = 0` encodes nothing, so `1⁰ = ε ∉ UHALT`.
* **Pairs.** "Encodes a pair `⟨M, x⟩` such that `M` halts on `x`" is `HALT c s = true`,
  i.e. `s = Turing.pairEncode α x` with `(c.decode α).toFinTM` halting on `x`. This inherits
  `HALT`'s conventions: the code comes first, and strings that are not pairs are not in it.
* **Representation scheme.** As for `HALT`, the scheme `c` is a parameter. Membership in
  `P/poly` holds for every scheme; undecidability is proved for every *effective* scheme
  (`Turing.EffectiveMachineCode`, which exists by `Turing.exists_effectiveMachineCode`),
  exactly the hypothesis of `Complexity.HALT_not_computable`.
* **Undecidability is stated in the machine model**: `¬ M.DecidesInTime (UHALT c) T` for
  every `M : Turing.FinTM Bool` and every `T : ℕ → ℕ`. `Complexity.EXP` and `Complexity.P` are
  unions of `DTIME` classes, each of which asks for such a decider.
* **Thm 6.6 enters as a hypothesis here, and is discharged downstream.**
  `Complexity.P_ssubset_PPoly_of_subset` takes `P ⊆ P/poly` as a hypothesis, which keeps
  this file independent of the tableau construction. [AB09, Thm 6.6] itself is
  `Complexity.P_subset_PPoly` (`CircuitComplexity/PSubsetPPoly.lean`), and the
  unconditional `P ⊊ P/poly` is `Complexity.P_ssubset_PPoly` there
  (`P_ssubset_PPoly_of_subset P_subset_PPoly`).

## Implementation notes

The reduction `HALT ≤ UHALT` needs a machine computing `s ↦ 1^{numOfString s}`. This takes
time exponential in `|s|`, which is fine because decidability puts no bound on time. No
composition combinator builds that loop. We take the machine from the proved
Mathlib-to-machine compiler `Turing.codePrim_machine` (`TuringMachine/MathlibBridge.lean`):
every `Primrec` string function is computed by some `FinTM Bool`. A bridge in the other
direction (machine-decidable implies `ComputablePred`) would instead let
`Language.not_computablePred_mem_uhalt` do the work; the library has no such bridge, so
the reduction is carried out in the machine model, which is the form the book's claim
(`UHALT ∉ P`, `UHALT ∉ EXP`) needs anyway.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5.1, Theorem 1.11; §6.1.1, p.110.)
-/

namespace Complexity

open Turing

/-! ### Binary expansions -/

/-- The binary expansion of `n`, most significant bit first (`true` for `1`). It is empty
for `n = 0` and starts with `true` otherwise. -/
def binaryExpansion (n : ℕ) : List Bool := n.bits.reverse

/-- The number whose binary expansion is `1s`: the string `s` read in binary behind a
leading `1`, so that trailing and leading `0`s of `s` are kept. -/
def numOfString (s : List Bool) : ℕ := s.reverse.foldr Nat.bit 1

/-- `xs.foldr Nat.bit 1` is positive (so `numOfString` is). -/
private lemma foldr_bit_one_pos (xs : List Bool) : 0 < xs.foldr Nat.bit 1 := by
  induction xs with
  | nil => exact Nat.one_pos
  | cons b xs ih =>
    change 0 < Nat.bit b (xs.foldr Nat.bit 1)
    cases b <;> simp [Nat.bit, ih]

/-- The bits (least significant first) of `foldr Nat.bit 1 xs` are `xs ++ [true]`. -/
private lemma bits_foldr_bit_one (xs : List Bool) :
    (xs.foldr Nat.bit 1).bits = xs ++ [true] := by
  induction xs with
  | nil => exact Nat.one_bits
  | cons b xs ih =>
    change (Nat.bit b (xs.foldr Nat.bit 1)).bits = (b :: xs) ++ [true]
    rw [Nat.bits_append_bit _ _ (fun h => (Nat.ne_of_gt (foldr_bit_one_pos xs) h).elim), ih]
    rfl

/-- The binary expansion of `numOfString s` is `1s`. -/
theorem binaryExpansion_numOfString (s : List Bool) :
    binaryExpansion (numOfString s) = true :: s := by
  rw [binaryExpansion, numOfString, bits_foldr_bit_one]
  simp

/-- `s ↦ 1^{numOfString s}` is primitive recursive (Mathlib's sense). -/
private lemma primrec_replicate_numOfString :
    Primrec fun s : List Bool => List.replicate (numOfString s) true := by
  have hbit : Primrec₂ Nat.bit := by
    apply (Primrec.cond Primrec.fst
      (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
      (Primrec.nat_double.comp Primrec.snd)).of_eq
    rintro ⟨b, n⟩
    cases b <;> simp [Nat.bit]
  have hnum : Primrec numOfString :=
    Primrec.list_foldr Primrec.list_reverse (Primrec.const 1)
      (hbit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))
  have hrep : Primrec fun n : ℕ => List.replicate n true :=
    (Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq fun n => by simp
  exact hrep.comp hnum

/-! ### The language `UHALT` -/

/-- `UHALT`, the unary halting language [AB09, p.110]: the words `1ⁿ` such that `n`'s
binary expansion is `1s` for a string `s` encoding a pair `⟨α, x⟩` (in `Turing.pairEncode`
format) whose machine `α` halts on input `x`, i.e. `Complexity.HALT c s = true`.

Divergence: the "encoding" of `s` by `n` is the leading-`1` convention, and the
representation scheme `c` is a parameter (see the module docstring). -/
def UHALT (c : MachineCode) : Language Bool :=
  Language.unary {n | ∃ s, binaryExpansion n = true :: s ∧ HALT c s = true}

/-- `UHALT` is unary. -/
theorem UHALT_le_allOnes (c : MachineCode) : UHALT c ≤ Language.allOnes :=
  Language.unary_le_allOnes _

/-- The reduction map is correct: `1^{numOfString s} ∈ UHALT` iff `HALT c s = true`. -/
theorem replicate_numOfString_mem_UHALT_iff (c : MachineCode) (s : List Bool) :
    List.replicate (numOfString s) true ∈ UHALT c ↔ HALT c s = true := by
  rw [UHALT, Language.replicate_mem_unary_iff, Set.mem_setOf_eq,
    binaryExpansion_numOfString]
  constructor
  · rintro ⟨s', hs', h⟩
    rw [List.cons.inj hs' |>.2]
    exact h
  · exact fun h => ⟨s, rfl, h⟩

/-- `UHALT ∈ P/poly`, as every unary language is [AB09, p.110 with Claim 6.8]. This holds
for every representation scheme. -/
theorem UHALT_mem_PPoly (c : MachineCode) : UHALT c ∈ BoolCircuit.PPoly :=
  Language.unary_inPPoly _

/-! ### Undecidability -/

/-- **The reduction `HALT ≤ UHALT`.** If a machine decides `UHALT` within some time bound
(any bound at all), then `HALT` is computable.

**Proof sketch.** `Turing.codePrim_machine` turns the primitive recursive map
`s ↦ 1^{numOfString s}` into a machine `R`. `Turing.FinTM.exists_comp_partial` composes `R`
with the decider `M` into a machine `D`. On input `s`, `R` halts with `1^{numOfString s}`,
and `M` then halts with the indicator bit of that word in `UHALT`. By
`replicate_numOfString_mem_UHALT_iff` that bit is `HALT c s`, so `D` computes
`s ↦ [HALT c s]`. -/
theorem HALT_computable_of_decidesInTime_UHALT (c : MachineCode) (M : FinTM Bool)
    (T : ℕ → ℕ) (hM : M.DecidesInTime (UHALT c) T) :
    Computable fun s => [HALT c s] := by
  classical
  obtain ⟨R, TR, hR⟩ := Turing.codePrim_machine _ primrec_replicate_numOfString
  obtain ⟨D, hD⟩ := FinTM.exists_comp_partial R M
  refine ⟨D, fun s => (hD s _).2
    ⟨List.replicate (numOfString s) true, ⟨_, hR s⟩, ⟨T (numOfString s), ?_⟩⟩⟩
  have hbit : MultiTapeTM.indicator (UHALT c : Set (List Bool))
      (List.replicate (numOfString s) true) = HALT c s := by
    unfold MultiTapeTM.indicator
    by_cases h : HALT c s = true
    · rw [if_pos ((replicate_numOfString_mem_UHALT_iff c s).2 h), h]
    · rw [if_neg (fun hm => h ((replicate_numOfString_mem_UHALT_iff c s).1 hm))]
      simpa using h
  show M.ComputesInTime _ [HALT c s] _
  rw [← hbit]
  simpa using hM (List.replicate (numOfString s) true)

/-- **`UHALT` is undecidable** [AB09, p.110]: for an effective representation scheme, no
finite binary machine decides `UHALT` within any time bound `T`. Otherwise
`Complexity.HALT_computable_of_decidesInTime_UHALT` would make `HALT` computable, which
contradicts [AB09, Theorem 1.11] (`Complexity.HALT_not_computable`). -/
theorem not_decidesInTime_UHALT (c : EffectiveMachineCode) (M : FinTM Bool)
    (T : ℕ → ℕ) : ¬ M.DecidesInTime (UHALT c.toMachineCode) T :=
  fun hM => HALT_not_computable c (HALT_computable_of_decidesInTime_UHALT _ M T hM)

/-- `UHALT` lies in no `DTIME` class. -/
theorem UHALT_not_mem_DTIME (c : EffectiveMachineCode) (T : ℕ → ℕ) :
    UHALT c.toMachineCode ∉ DTIME T := by
  rintro ⟨a, M, hM⟩
  exact not_decidesInTime_UHALT c M _ hM

/-- **`UHALT ∉ EXP`** [AB09, p.110: "not in `P` (or for that matter in `EXP`)"]. -/
theorem UHALT_not_mem_EXP (c : EffectiveMachineCode) : UHALT c.toMachineCode ∉ EXP := by
  intro h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  exact UHALT_not_mem_DTIME c _ hk

/-- **`UHALT ∉ P`** [AB09, p.110], via `Complexity.P_subset_EXP`. -/
theorem UHALT_not_mem_P (c : EffectiveMachineCode) : UHALT c.toMachineCode ∉ P :=
  fun h => UHALT_not_mem_EXP c (P_subset_EXP h)

/-! ### `P/poly` against `P` and `EXP` -/

/-- **Some language in `P/poly` is not in `EXP`** [AB09, p.110]. The witness is `UHALT`
over the effective scheme of `Turing.exists_effectiveMachineCode`; it is unary. -/
theorem exists_mem_PPoly_not_mem_EXP : ∃ L ∈ BoolCircuit.PPoly, L ∉ EXP := by
  obtain ⟨c⟩ := exists_effectiveMachineCode
  exact ⟨UHALT c.toMachineCode, UHALT_mem_PPoly _, UHALT_not_mem_EXP c⟩

/-- `P/poly` is not contained in `EXP`. -/
theorem PPoly_not_subset_EXP : ¬ BoolCircuit.PPoly ⊆ EXP := by
  obtain ⟨L, hL, hLE⟩ := exists_mem_PPoly_not_mem_EXP
  exact fun h => hLE (h hL)

/-- `P/poly` is not contained in `P`. -/
theorem PPoly_not_subset_P : ¬ BoolCircuit.PPoly ⊆ P :=
  fun h => PPoly_not_subset_EXP (h.trans P_subset_EXP)

/-- **The inclusion `P ⊆ P/poly` is proper** [AB09, p.110]. The inclusion itself
(Theorem 6.6) is the hypothesis. Properness comes from `UHALT`, which is in `P/poly`
but not in `EXP ⊇ P`. -/
theorem P_ssubset_PPoly_of_subset (h : P ⊆ BoolCircuit.PPoly) : P ⊂ BoolCircuit.PPoly :=
  Set.ssubset_iff_subset_ne.mpr ⟨h, fun heq => PPoly_not_subset_P heq.ge⟩

end Complexity
