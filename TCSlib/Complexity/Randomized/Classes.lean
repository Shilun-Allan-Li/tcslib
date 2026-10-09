/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The randomized complexity classes BPP, RP, coRP, ZPP

Verifier-style definitions of Arora–Barak's randomized complexity classes,
following the certificate view of [AB09, Def 7.4]: a language is in a
randomized class when some efficient two-input predicate `M(x, r)`, run on the
input `x` and a uniformly random string `r` of polynomially-bounded length,
decides membership with the class's acceptance-probability profile.

## Main definitions

* `Randomized.randProb` — the probability of an event over a uniform random
  string of a given length, as a rational counting ratio.
* `Randomized.polyLen` — the canonical polynomial length schedule
  `n ↦ a·(n+1)^k` for random strings.
* `Randomized.VerifierModel` — an abstract *efficiency notion* standing in for
  "polynomial-time Turing machine" (see **Deviations** below).
* `Randomized.InBPP` — [AB09, Def 7.4] (equivalently Def 7.1 via the
  certificate view).
* `Randomized.InRP`, `Randomized.InCoRP` — [AB09, Def 7.6] and the remark
  following it.
* `Randomized.InZPP` — [AB09, Def 7.7], in the zero-error "abort"
  formulation (see **Deviations**).
* `Randomized.raceVerifier`, `Randomized.majorityVerifier` — the two verifier
  constructions used by Theorems 7.8 and 7.10.

## Main results

* `Randomized.inZPP_iff_inRP_and_inCoRP` — `ZPP = RP ∩ coRP` [AB09, Thm 7.8].
* `Randomized.InBPP.compl` — `BPP = coBPP` (used by [AB09, Thm 7.18]).
* `Randomized.bpp_error_reduction` — error reduction [AB09, Thm 7.10].
* `Randomized.inBPPWeak_iff_inBPP` — `BPP_{n^{-c}} = BPP` [AB09, Lem 7.9].

## Deviations from the source

* **Machine model.** [AB09] defines these classes with polynomial-time Turing
  machines.  Per the repository's agreed scope, we use the certificate view of
  [AB09, Def 7.4] — predicates over inputs and random strings — and replace
  "`M` is a polynomial-time TM" by membership in an abstract
  `VerifierModel` `E`, a predicate on verifiers.  Every class and theorem is
  parametrized by `E`.  The closure properties that [AB09]'s proofs use
  (building the race, majority, complement, and projection verifiers out of
  given ones) are stated as explicit named hypotheses (`ClosedUnder…`), all of
  which hold for the intended instantiation "computable in polynomial time".
  Intended instantiation targets, once a uniform-computability layer is
  available: the `P`/`PolyTime` development of the `complexity/arora-barak-ch1`
  branch, or Mathlib's `Turing.TM2ComputableInPolyTime`.
* **Length schedules.** [AB09, Def 7.4] draws `r ∈ {0,1}^{p(|x|)}` for a
  polynomial `p`.  We fix the canonical schedule `polyLen a k : n ↦ a·(n+1)^k`
  (existentially quantified over `a, k : ℕ`) rather than an arbitrary
  `p : ℕ → ℕ` with a polynomial bound: an arbitrary bounded `p` need not be
  computable and could smuggle undecidable information through the schedule
  itself.  Every polynomial is dominated by some `polyLen a k`, and a verifier
  can ignore padding bits, so the class is unchanged.
* **Probability.** `Pr_{r ∈ {0,1}^m}` is the counting ratio
  `#{r : accepted}/2^m` valued in `ℚ`; random strings of length `m` are
  `Fin m → Bool`, passed to verifiers as lists via `List.ofFn`.
* **ZPP.** [AB09, Def 7.7] defines `ZPP` by expected running time of a
  zero-error machine.  Expected time is not expressible for abstract
  predicates, so we use the standard equivalent "Las Vegas" formulation: a
  verifier with values in `Option Bool` that is never wrong and outputs `none`
  ("don't know") with probability at most `1/2`.  [AB09, §7.4.2] sketches the
  equivalence of expected-time and worst-case formulations (truncation via
  Markov's inequality).
* **The weak threshold of Lemma 7.9.** The book's success threshold
  `1/2 + |x|^{-c}` exceeds `1` for `|x| ≤ 1`, making the literal class
  `BPP_{n^{-c}}` empty; we require advantage `min (1/6) ((|x|+1)^{-c})`
  instead, which for `c ≥ 1` agrees with the book's (up to the `n+1` shift) for
  `|x| ≥ 5` and makes `BPP ⊆ BPP_{n^{-c}}` hold as the book intends.
* The constant `2/3` follows [AB09, Defs 7.1/7.6]; `1/2` in `InZPP` is the
  conventional choice (any constant in `(0,1)` gives the same class, by the
  same repetition argument as [AB09, §7.4.1]).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability, over a uniformly random string `r ∈ {0,1}^m`, that the
event `A` holds of `r` (as a list): the counting ratio `#{r : A r}/2^m`.
[AB09, Def 7.4: "`Pr_{r ∈_R {0,1}^{p(|x|)}}`"] -/
def randProb (m : ℕ) (A : List Bool → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m

/-- Two events that agree on every random string have the same
probability. -/
theorem randProb_congr {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) ↔ B (List.ofFn r)) :
    randProb m A = randProb m B := by
  unfold randProb
  rw [Finset.filter_congr fun r _ => h r]

/-- Probabilities are nonnegative. -/
theorem randProb_nonneg {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    0 ≤ randProb m A := by
  unfold randProb
  positivity

/-- There are `2^m` random strings of length `m`. -/
theorem card_univ_bitstrings (m : ℕ) :
    (univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Probabilities are at most one. -/
theorem randProb_le_one {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    randProb m A ≤ 1 := by
  unfold randProb
  rw [div_le_one (by positivity)]
  calc ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
      ≤ ((univ : Finset (Fin m → Bool)).card : ℚ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = 2 ^ m := by rw [card_univ_bitstrings]; push_cast; rfl

/-- Probability is monotone in the event. -/
theorem randProb_mono {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) → B (List.ofFn r)) :
    randProb m A ≤ randProb m B := by
  unfold randProb
  gcongr
  exact h _

/-- Complement rule: `Pr[¬A] = 1 − Pr[A]`. -/
theorem randProb_not {m : ℕ} (A : List Bool → Prop) [DecidablePred A] :
    randProb m (fun l => ¬ A l) = 1 - randProb m A := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin m → Bool))) (p := fun r => A (List.ofFn r))
  rw [card_univ_bitstrings] at hsplit
  have h2 : ((2 : ℚ) ^ m) ≠ 0 := by positivity
  have hcast : ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
      = 2 ^ m - ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) := by
    have h3 : ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
        + ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
        = 2 ^ m := by
      exact_mod_cast hsplit
    linarith
  show ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ) / 2 ^ m
      = 1 - randProb m A
  unfold randProb
  rw [hcast, sub_div, div_self h2]

/-- The certain event has probability one. -/
theorem randProb_true {m : ℕ} : randProb m (fun _ => True) = 1 := by
  unfold randProb
  rw [Finset.filter_true_of_mem fun _ _ => trivial, card_univ_bitstrings]
  push_cast
  exact div_self (by positivity)

/-- Every list of length `m` arises from a tuple of `m` bits. -/
theorem exists_ofFn_eq {l : List Bool} {m : ℕ} (h : l.length = m) :
    ∃ r : Fin m → Bool, l = List.ofFn r := by
  refine ⟨fun i => l[(i : ℕ)]'(by omega), ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

/-- **Independence of disjoint segments**: if the event is a conjunction of a
condition on the first `m₁` bits and a condition on the remaining `m₂` bits,
the probability factors. -/
theorem randProb_split (m₁ m₂ : ℕ) (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B] :
    randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ B (r.drop m₁)) =
      randProb m₁ A * randProb m₂ B := by
  unfold randProb
  rw [div_mul_div_comm, ← pow_add, ← Nat.cast_mul]
  congr 2
  rw [← Finset.card_product]
  refine (Finset.card_bij (fun uv _ => Fin.append uv.1 uv.2) ?_ ?_ ?_).symm
  · rintro ⟨u, v⟩ huv
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at huv
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [List.ofFn_fin_append, List.take_left' (by simp)]
      exact huv.1.2
    · rw [List.ofFn_fin_append, List.drop_left' (by simp)]
      exact huv.2.2
  · intro uv huv uv' huv' h
    exact (Fin.appendEquiv m₁ m₂).injective (by exact h)
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hA, hB⟩ := hr
    have hdec : Fin.append (fun i => r (Fin.castAdd m₂ i))
        (fun i => r (Fin.natAdd m₁ i)) = r := Fin.append_castAdd_natAdd
    refine ⟨(fun i => r (Fin.castAdd m₂ i), fun i => r (Fin.natAdd m₁ i)),
      ?_, hdec⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    rw [← hdec, List.ofFn_fin_append] at hA hB
    rw [List.take_left' (by simp)] at hA
    rw [List.drop_left' (by simp)] at hB
    exact ⟨⟨Finset.mem_univ _, hA⟩, Finset.mem_univ _, hB⟩

/-- A condition on only the first `m₁ ≤ m` bits has the same probability over
`m`-bit strings as over `m₁`-bit strings: padding bits are ignored. -/
theorem randProb_take {m₁ m : ℕ} (h : m₁ ≤ m) (A : List Bool → Prop)
    [DecidablePred A] :
    randProb m (fun r => A (r.take m₁)) = randProb m₁ A := by
  obtain ⟨m₂, rfl⟩ := Nat.exists_eq_add_of_le h
  calc randProb (m₁ + m₂) (fun r => A (r.take m₁))
      = randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ (fun _ => True) (r.drop m₁)) :=
        randProb_congr fun r => by simp
    _ = randProb m₁ A * randProb m₂ (fun _ => True) :=
        randProb_split m₁ m₂ A (fun _ => True)
    _ = randProb m₁ A := by rw [randProb_true, mul_one]

/-- The canonical polynomial length schedule `n ↦ a·(n+1)^k` for random
strings — a concrete, computable stand-in for [AB09, Def 7.4]'s "polynomial
`p`" (see the module docstring's **Deviations**: an arbitrary polynomially
*bounded* `ℕ → ℕ` need not be computable and would let the schedule itself
decide undecidable languages). -/
def polyLen (a k : ℕ) : ℕ → ℕ := fun n => a * (n + 1) ^ k

/-- An abstract *efficiency notion* for verifiers, standing in for
"polynomial-time Turing machine" in [AB09, Def 7.4] (see the module
docstring's **Deviations**).  `Eff M` reads "`M` is an efficient verifier";
verifiers are `Option Bool`-valued so that zero-error ("don't know") verifiers
and ordinary Boolean verifiers share one notion.  `EffTwoWitness N` is the
corresponding notion for predicates of an input and two witness strings, the
verifier format of `Σ₂`-statements (used by [AB09, Thm 7.18]).  Intended
instantiations: a polynomial-time TM layer (the `complexity/arora-barak-ch1`
branch's `PolyTime`, or Mathlib's `Turing.TM2ComputableInPolyTime`). -/
structure VerifierModel where
  /-- "`M` is an efficient (poly-time) verifier." -/
  Eff : (List Bool → List Bool → Option Bool) → Prop
  /-- "`N` is an efficient (poly-time) two-witness predicate." -/
  EffTwoWitness : (List Bool → List Bool → List Bool → Bool) → Prop

/-- A Boolean verifier, viewed as an `Option Bool`-valued one. -/
def boolVerifier (M : List Bool → List Bool → Bool) :
    List Bool → List Bool → Option Bool :=
  fun x r => some (M x r)

variable (E : VerifierModel)

/-- `L ∈ BPP`: some efficient verifier `M` with polynomially-long randomness
decides `L` with two-sided error at most `1/3` — for every input `x`,
`Pr_{r ∈ {0,1}^{p(|x|)}}[M(x,r) = L(x)] ≥ 2/3`, where `p = polyLen a k`.
[AB09, Def 7.4] (the certificate form of [AB09, Def 7.1]). -/
def InBPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
def InRP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) = false)

/-- `L ∈ coRP` iff its complement is in `RP`: one-sided error in the other
direction.  [AB09, §7.3: "`coRP = {L | L̄ ∈ RP}`"] -/
def InCoRP (L : Language Bool) : Prop :=
  InRP E Lᶜ

/-- `L ∈ ZPP`: some efficient zero-error verifier decides `L` — it may output
`none` ("don't know") with probability at most `1/2`, but whenever it outputs
an answer, the answer is correct.  [AB09, Def 7.7], in the equivalent
Las Vegas formulation (see the module docstring's **Deviations**). -/
def InZPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
    E.Eff M ∧
    ∀ x : List Bool,
      (x ∈ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some false) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some true) ∧
      randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2

section Constructions

/-- The *race* of an `RP` verifier for `L` and an `RP` verifier for `Lᶜ` on
split randomness: on `r = r₁ ++ r₂`, answer `some true` if `M₁` accepts `r₁`,
else `some false` if `M₂` accepts `r₂`, else `none`.  The construction behind
`RP ∩ coRP ⊆ ZPP` in [AB09, Thm 7.8]. -/
def raceVerifier (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if M₁ x (r.take (p₁ x.length)) then some true
  else if M₂ x (r.drop (p₁ x.length)) then some false
  else none

/-- The `k`-fold repetition of a verifier with majority vote, on randomness
split into `k` blocks of length `p(|x|)`: the construction behind error
reduction [AB09, Thm 7.10]. -/
def majorityVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  let n := x.length
  let votes := (List.range (k n)).countP fun i =>
    M x ((r.drop (i * p n)).take (p n))
  k n < 2 * votes

/-- `E` can race two of its Boolean verifiers on a polynomial split point
(closure of polynomial time under running two machines on split
randomness). -/
def ClosedUnderRace : Prop :=
  ∀ M₁ M₂ a k, E.Eff (boolVerifier M₁) → E.Eff (boolVerifier M₂) →
    E.Eff (raceVerifier M₁ M₂ (polyLen a k))

/-- `E` can turn a zero-error verifier into the Boolean verifier answering
"did it output `some b`?" (closure of polynomial time under postprocessing
the output). -/
def ClosedUnderAnswerIs : Prop :=
  ∀ M b, E.Eff M →
    E.Eff (boolVerifier fun x r => M x r = some b)

/-- The `k`-fold repetition of a verifier accepting if *any* repetition
accepts, on randomness split into `k` blocks of length `p(|x|)`: the
one-sided amplifier (an `OR`, not a majority — a strict majority cannot
amplify success probability exactly `1/2`, whereas for one-sided error the
`OR` drives the failure probability to `(1/2)^k` without hurting
soundness).  Used by [AB09, Thm 7.8]'s `ZPP ⊆ RP` direction. -/
def anyVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  (List.range (k x.length)).any fun i =>
    M x ((r.drop (i * p x.length)).take (p x.length))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and take the majority (closure of polynomial time under
polynomial repetition). -/
def ClosedUnderMajority : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (majorityVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and accept if any repetition accepts (closure of
polynomial time under polynomial repetition with an `OR`). -/
def ClosedUnderAny : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (anyVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can negate a Boolean verifier's answer (closure of polynomial time
under complementation of the output). -/
def ClosedUnderNot : Prop :=
  ∀ M, E.Eff (boolVerifier M) →
    E.Eff (boolVerifier fun x r => !(M x r))

end Constructions

section Counting

/-- `Pr[∅] = 0`. -/
theorem randProb_false {m : ℕ} : randProb m (fun _ => False) = 0 := by
  unfold randProb
  rw [Finset.filter_false]
  simp

/-- Additivity over disjoint events. -/
theorem randProb_or_disjoint {m : ℕ} (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B]
    (h : ∀ r : Fin m → Bool, ¬ (A (List.ofFn r) ∧ B (List.ofFn r))) :
    randProb m (fun l => A l ∨ B l) = randProb m A + randProb m B := by
  unfold randProb
  rw [← add_div, ← Nat.cast_add]
  congr 2
  rw [Finset.filter_or]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro r hrA hrB
  rw [Finset.mem_filter] at hrA hrB
  exact h r ⟨hrA.2, hrB.2⟩

/-- Partitioning by the value of a natural-number statistic. -/
theorem randProb_mem_eq_sum {m : ℕ} (g : List Bool → ℕ) (T : Finset ℕ) :
    randProb m (fun l => g l ∈ T) = ∑ j ∈ T, randProb m (fun l => g l = j) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,
      randProb_congr (B := fun _ => False) fun r => by simp]
    exact randProb_false
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih,
      randProb_congr (B := fun l => g l = a ∨ g l ∈ T) fun r => by
        simp [Finset.mem_insert]]
    exact randProb_or_disjoint _ _ fun r ⟨h1, h2⟩ => ha (h1 ▸ h2)

/-- `Pr[B = false] = 1 − Pr[B = true]` for a Boolean test. -/
theorem randProb_bool_false {m : ℕ} (B : List Bool → Bool) :
    randProb m (fun l => B l = false) =
      1 - randProb m (fun l => B l = true) := by
  rw [randProb_congr (B := fun l => ¬ (B l = true)) fun r => by simp]
  exact randProb_not _

/-- The number of the `K` successive length-`q` blocks of `l` on which the
Boolean test `B` succeeds: the vote count of `majorityVerifier` and
`anyVerifier`, abstracted over the test. -/
def blockCount (q K : ℕ) (B : List Bool → Bool) (l : List Bool) : ℕ :=
  (List.range K).countP fun i => B ((l.drop (i * q)).take q)

theorem blockCount_le (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q K B l ≤ K := by
  calc blockCount q K B l ≤ (List.range K).length := List.countP_le_length ..
    _ = K := List.length_range ..

/-- Peeling off the first block. -/
theorem blockCount_succ (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q (K + 1) B l =
      (if B (l.take q) then 1 else 0) + blockCount q K B (l.drop q) := by
  unfold blockCount
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have hfun : ((fun i => B ((l.drop (i * q)).take q)) ∘ Nat.succ)
      = fun i => B (((l.drop q).drop (i * q)).take q) := by
    funext i
    simp only [Function.comp_apply]
    rw [Nat.succ_mul, Nat.add_comm (i * q) q, ← List.drop_drop]
  rw [hfun, zero_mul, List.drop_zero]
  exact Nat.add_comm _ _

/-- **The vote count is binomially distributed**: over a uniform string of
`K` blocks of `q` bits each, `Pr[blockCount = j] = C(K,j)·s^j·(1−s)^{K−j}`,
where `s` is the single-block success probability. -/
theorem randProb_blockCount (q : ℕ) (B : List Bool → Bool) :
    ∀ K j : ℕ, j ≤ K →
      randProb (K * q) (fun l => blockCount q K B l = j) =
        (K.choose j : ℚ) * (randProb q (fun l => B l = true)) ^ j *
          (1 - randProb q (fun l => B l = true)) ^ (K - j)
  | 0, 0, _ => by
    rw [randProb_congr (B := fun _ => True) fun r => by simp [blockCount],
      randProb_true]
    simp
  | 0, j + 1, h => absurd h (by omega)
  | K + 1, 0, _ => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q) (fun l => blockCount q (K + 1) B l = 0)
        = randProb (q + K * q) (fun l =>
            (fun l' => B l' = false) (l.take q) ∧
            (fun w => blockCount q K B w = 0) (l.drop q)) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb]
    rw [hev, randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = 0),
      randProb_bool_false, randProb_blockCount q B K 0 (by omega)]
    simp [pow_succ]
    ring
  | K + 1, j + 1, h => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q)
        (fun l => blockCount q (K + 1) B l = j + 1)
        = randProb (q + K * q) (fun l =>
            ((fun l' => B l' = true) (l.take q) ∧
              (fun w => blockCount q K B w = j) (l.drop q)) ∨
            ((fun l' => B l' = false) (l.take q) ∧
              (fun w => blockCount q K B w = j + 1) (l.drop q))) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb] <;> omega
    rw [hev, randProb_or_disjoint _ _ (fun r => by
      rintro ⟨⟨h1, -⟩, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by simp)),
      randProb_split q (K * q) (fun l' => B l' = true)
        (fun w => blockCount q K B w = j),
      randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = j + 1),
      randProb_bool_false]
    rcases Nat.lt_or_ge j K with hjK | hjK
    · rw [randProb_blockCount q B K j (by omega),
        randProb_blockCount q B K (j + 1) (by omega)]
      have hpascal : (((K + 1).choose (j + 1) : ℕ) : ℚ)
          = (K.choose j : ℚ) + (K.choose (j + 1) : ℚ) := by
        exact_mod_cast Nat.choose_succ_succ K j
      have he1 : K + 1 - (j + 1) = K - j := by omega
      have he2 : K - j = (K - (j + 1)) + 1 := by omega
      rw [he1, hpascal, he2, pow_succ]
      ring
    · have hjeq : j = K := by omega
      rw [hjeq, randProb_blockCount q B K K (le_refl _)]
      have hzero : randProb (K * q)
          (fun w => blockCount q K B w = K + 1) = 0 := by
        rw [randProb_congr (B := fun _ => False) fun r => by
          have := blockCount_le q K B (List.ofFn r)
          simp
          omega]
        exact randProb_false
      rw [hzero, mul_zero, add_zero]
      simp [Nat.choose_self, pow_succ]
      ring

/-- **Elementary Chernoff-type tail bound** for the vote count: if each
block succeeds with probability at most `1/2 − ε`, then at least half of
the `K` blocks succeed with probability at most `2·(1 − 4ε²)^⌊K/2⌋`.
(The elementary `2^K·(s(1−s))^{⌊K/2⌋}` estimate; no exponential function
is needed, which keeps the whole development inside `ℚ`.) -/
theorem randProb_tail_le (q K : ℕ) (B : List Bool → Bool) {ε : ℚ}
    (hε0 : 0 ≤ ε) (hs : randProb q (fun l => B l = true) ≤ 1/2 - ε) :
    randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l) ≤
      2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
  have hs0 : (0:ℚ) ≤ randProb q (fun l => B l = true) := randProb_nonneg
  have hs1 : randProb q (fun l => B l = true) ≤ 1 := randProb_le_one
  set s : ℚ := randProb q (fun l => B l = true) with hs_def
  have hf0 : (0:ℚ) ≤ 1 - s := by linarith
  have hεhalf : ε ≤ 1/2 := by linarith
  set T : Finset ℕ := (Finset.range (K + 1)).filter (fun j => K ≤ 2 * j)
    with hT
  have hev : randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l)
      = ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j) := by
    rw [← randProb_mem_eq_sum (fun l => blockCount q K B l) T]
    refine randProb_congr fun r => ?_
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨Nat.lt_succ_of_le (blockCount_le q K B _), h⟩
    · exact fun h => h.2
  rw [hev]
  have hterm : ∀ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := by
    intro j hj
    rw [hT, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjK, hKj⟩ := hj
    have hjK' : j ≤ K := by omega
    rw [randProb_blockCount q B K j hjK', ← hs_def]
    have hj₀ : K - K / 2 ≤ j := by omega
    have hsf : s ≤ 1 - s := by linarith
    -- shift the exponent towards the balanced point
    have hstep1 : s ^ j * (1 - s) ^ (K - j)
        ≤ s ^ (K - K / 2) * (1 - s) ^ (K / 2) := by
      have e1 : s ^ j = s ^ (K - K / 2) * s ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      have e2 : (1 - s) ^ (K / 2)
          = (1 - s) ^ (K - j) * (1 - s) ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1, e2]
      have hpow : s ^ (j - (K - K / 2)) ≤ (1 - s) ^ (j - (K - K / 2)) :=
        pow_le_pow_left₀ hs0 hsf _
      calc s ^ (K - K / 2) * s ^ (j - (K - K / 2)) * (1 - s) ^ (K - j)
          ≤ s ^ (K - K / 2) * (1 - s) ^ (j - (K - K / 2)) *
              (1 - s) ^ (K - j) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
        _ = s ^ (K - K / 2) * ((1 - s) ^ (K - j) *
              (1 - s) ^ (j - (K - K / 2))) := by ring
    have hstep2 : s ^ (K - K / 2) * (1 - s) ^ (K / 2)
        ≤ (s * (1 - s)) ^ (K / 2) := by
      have e3 : s ^ (K - K / 2) = s ^ (K / 2) * s ^ (K - 2 * (K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e3, mul_pow]
      have hle1 : s ^ (K - 2 * (K / 2)) ≤ 1 := pow_le_one₀ hs0 hs1
      calc s ^ (K / 2) * s ^ (K - 2 * (K / 2)) * (1 - s) ^ (K / 2)
          ≤ s ^ (K / 2) * 1 * (1 - s) ^ (K / 2) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hle1 (by positivity)) (by positivity)
        _ = s ^ (K / 2) * (1 - s) ^ (K / 2) := by ring
    have hmono := hstep1.trans hstep2
    calc (K.choose j : ℚ) * s ^ j * (1 - s) ^ (K - j)
        = (K.choose j : ℚ) * (s ^ j * (1 - s) ^ (K - j)) := by ring
      _ ≤ (K.choose j : ℚ) * ((s * (1 - s)) ^ (K / 2)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  have hTsub : T ⊆ Finset.range (K + 1) := by
    rw [hT]
    exact Finset.filter_subset _ _
  have hsum2 : ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsub fun j _ _ => by positivity
  have hsum3 : ∑ j ∈ Finset.range (K + 1),
      (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hprod : s * (1 - s) ≤ 1/4 - ε ^ 2 := by nlinarith
  have hprod0 : (0:ℚ) ≤ s * (1 - s) := by positivity
  have hfinal : (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
      ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
    have h2K : (2 : ℚ) ^ K ≤ 2 * 4 ^ (K / 2) := by
      have e4 : K = 2 * (K / 2) + K % 2 := by omega
      calc (2 : ℚ) ^ K = 2 ^ (2 * (K / 2)) * 2 ^ (K % 2) := by
            rw [← pow_add, ← e4]
        _ ≤ 2 ^ (2 * (K / 2)) * 2 ^ 1 := by
            refine mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
        _ = 2 * 4 ^ (K / 2) := by
            rw [pow_mul]
            norm_num
            ring
    have hpow : (s * (1 - s)) ^ (K / 2) ≤ (1/4 - ε ^ 2) ^ (K / 2) :=
      pow_le_pow_left₀ hprod0 hprod _
    calc (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
        ≤ (2 * 4 ^ (K / 2)) * (1/4 - ε ^ 2) ^ (K / 2) := by
          refine mul_le_mul h2K hpow (by positivity) (by positivity)
      _ = 2 * (4 * (1/4 - ε ^ 2)) ^ (K / 2) := by
          rw [mul_pow]
          ring
      _ = 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
          congr 2
          ring
  calc ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := hsum2
    _ = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := hsum3
    _ ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := hfinal

/-- The rational Bernoulli estimate `(1−x)^m ≤ 1/2` once `m·x ≥ 1`:
`(1−x)^m·(1+mx) ≤ 1` by induction, and `1+mx ≥ 2`. -/
theorem one_sub_pow_le_half {x : ℚ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ}
    (hm : 1 ≤ (m : ℚ) * x) : (1 - x) ^ m ≤ 1/2 := by
  have key : ∀ m' : ℕ, (1 - x) ^ m' * (1 + (m' : ℚ) * x) ≤ 1 := by
    intro m'
    induction m' with
    | zero => simp
    | succ m' ih =>
      have h1 : (0:ℚ) ≤ (1 - x) ^ m' := pow_nonneg (by linarith) m'
      have hstep : (1 - x) * (1 + ((m' : ℚ) + 1) * x) ≤ 1 + (m' : ℚ) * x := by
        have hnn : 0 ≤ ((m' : ℚ) + 1) * x ^ 2 := by positivity
        have hexp : (1 - x) * (1 + ((m' : ℚ) + 1) * x)
            = 1 + (m' : ℚ) * x - ((m' : ℚ) + 1) * x ^ 2 := by ring
        rw [hexp]
        linarith
      calc (1 - x) ^ (m' + 1) * (1 + ((m' + 1 : ℕ) : ℚ) * x)
          = (1 - x) ^ m' * ((1 - x) * (1 + ((m' : ℚ) + 1) * x)) := by
            push_cast
            ring
        _ ≤ (1 - x) ^ m' * (1 + (m' : ℚ) * x) :=
            mul_le_mul_of_nonneg_left hstep h1
        _ ≤ 1 := ih
  have h3 := key m
  nlinarith [pow_nonneg (by linarith : (0:ℚ) ≤ 1 - x) m]

/-- Iterating `one_sub_pow_le_half`: `(1−x)^e ≤ (1/2)^T` once `e ≥ m·T`
with `m·x ≥ 1`. -/
theorem one_sub_pow_le_half_pow {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {m T e : ℕ} (hm : 1 ≤ (m : ℚ) * x) (he : m * T ≤ e) :
    (1 - x) ^ e ≤ (1/2 : ℚ) ^ T := by
  calc (1 - x) ^ e ≤ (1 - x) ^ (m * T) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) he
    _ = ((1 - x) ^ m) ^ T := by rw [pow_mul]
    _ ≤ (1/2 : ℚ) ^ T :=
      pow_le_pow_left₀ (pow_nonneg (by linarith) m)
        (one_sub_pow_le_half hx0 hx1 hm) T

end Counting

/-- `BPP` is closed under complementation (`BPP = coBPP`): swap the two
acceptance clauses and negate the verifier's answer.  Used by
[AB09, Thm 7.18]'s proof ("it is enough to prove `BPP ⊆ Σ₂ᵖ` because `BPP`
is closed under complementation").

**Proof sketch.** If `M` decides `L` with two-sided error `1/3`, then
`¬M` decides `Lᶜ` with the same error: the `x ∈ Lᶜ` clause for `¬M` is the
`x ∉ L` clause for `M` and vice versa, since
`¬M x r = true ↔ M x r = false`. -/
theorem InBPP.compl (hNot : ClosedUnderNot E) {L : Language Bool}
    (hL : InBPP E L) : InBPP E Lᶜ := by
  obtain ⟨M, a, k, hM, hacc⟩ := hL
  refine ⟨fun x r => !(M x r), a, k, hNot M hM, fun x => ?_⟩
  constructor
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = false :=
          (hacc x).2 hx
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = true :=
          randProb_congr fun r => by simp
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = true :=
          (hacc x).1 (Set.not_notMem.mp hx)
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = false :=
          randProb_congr fun r => by simp

/-- From a zero-error verifier whose definite answers are never wrong, a
one-sided witness: on members it answers `some b` with probability at least
`1/2` (it never answers `some (!b)` and aborts with probability at most
`1/2`), and on non-members it never answers `some b`; a 2-fold `OR`
(`anyVerifier`) amplifies `1/2` to `3/4 ≥ 2/3`.  The common core of the
inclusions `ZPP ⊆ RP` and `ZPP ⊆ coRP` in [AB09, Thm 7.8]. -/
theorem inRP_of_zeroError (hAns : ClosedUnderAnswerIs E)
    (hAny : ClosedUnderAny E) {M : List Bool → List Bool → Option Bool}
    {a k : ℕ} (hM : E.Eff M) (L' : Language Bool) (b : Bool)
    (hin : ∀ x ∈ L', (∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some (!b)) ∧
        randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2)
    (hout : ∀ x ∉ L', ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some b) :
    InRP E L' := by
  classical
  refine ⟨anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
    (polyLen 2 0), 2 * a, k, hAny _ a k 2 0 (hAns M b hM), fun x => ?_⟩
  have hlen : polyLen (2 * a) k x.length
      = polyLen a k x.length + polyLen a k x.length := by
    unfold polyLen
    ring
  -- Unfold the 2-fold `OR` on an arbitrary random string.
  have hN_iff : ∀ l : List Bool,
      anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
          (polyLen 2 0) x l = true ↔
        (M x (l.take (polyLen a k x.length)) = some b ∨
          M x ((l.drop (polyLen a k x.length)).take
            (polyLen a k x.length)) = some b) := by
    intro l
    unfold anyVerifier
    rw [show polyLen 2 0 x.length = 2 from by unfold polyLen; ring,
      show List.range 2 = [0, 1] from rfl]
    simp
  constructor
  · -- members are accepted with probability at least `3/4`
    intro hx
    obtain ⟨hnever, habort⟩ := hin x hx
    -- one run answers `some b` with probability at least `1/2`
    have hone : 1/2 ≤ randProb (polyLen a k x.length)
        (fun l => M x l = some b) := by
      have hmono : randProb (polyLen a k x.length)
          (fun l => ¬ (M x l = none)) ≤
          randProb (polyLen a k x.length) (fun l => M x l = some b) := by
        refine randProb_mono fun r hr => ?_
        rcases hcase : M x (List.ofFn r) with _ | b'
        · exact absurd hcase hr
        · have hb' : b' ≠ !b := fun h => hnever r (h ▸ hcase)
          have hbb : b' = b := by cases b <;> cases b' <;> simp_all
          rw [hbb]
      have hnot := randProb_not (m := polyLen a k x.length)
        (fun l => M x l = none)
      linarith
    rw [hlen]
    have hstep1 : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length + polyLen a k x.length)
          (fun l => (fun l' => ¬ (M x l' = some b))
              (l.take (polyLen a k x.length)) ∧
            (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
              (l.drop (polyLen a k x.length))) :=
      randProb_congr fun rr => by
        rw [hN_iff (List.ofFn rr)]
        exact not_or
    have hstep2 := randProb_split (polyLen a k x.length) (polyLen a k x.length)
      (fun l' => ¬ (M x l' = some b))
      (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
    have hstep3 := randProb_take (le_refl (polyLen a k x.length))
      (fun l' => ¬ (M x l' = some b))
    have hfail : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
          randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) := by
      rw [hstep1, hstep2, hstep3]
    have hs_le : randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) ≤ 1/2 := by
      rw [randProb_not]
      linarith
    have hs_nonneg : (0 : ℚ) ≤ randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) := randProb_nonneg
    have hfail_le : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) ≤ 1/4 := by
      rw [hfail]
      calc randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
            randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b))
          ≤ (1/2) * (1/2) := mul_le_mul hs_le hs_le hs_nonneg (by norm_num)
        _ = 1/4 := by norm_num
    have hnotN := randProb_not
      (m := polyLen a k x.length + polyLen a k x.length)
      (fun l => anyVerifier (fun x r => decide (M x r = some b))
        (polyLen a k) (polyLen 2 0) x l = true)
    linarith
  · -- non-members are never accepted
    intro hx rr
    rw [Bool.eq_false_iff]
    intro hacc
    rw [hN_iff (List.ofFn rr)] at hacc
    have hlen' : (List.ofFn rr).length
        = polyLen a k x.length + polyLen a k x.length := by
      rw [List.length_ofFn, hlen]
    rcases hacc with h | h
    · have hb1 : ((List.ofFn rr).take (polyLen a k x.length)).length
          = polyLen a k x.length := by
        rw [List.length_take, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb1
      rw [hr'] at h
      exact hout x hx r' h
    · have hb2 : (((List.ofFn rr).drop (polyLen a k x.length)).take
          (polyLen a k x.length)).length = polyLen a k x.length := by
        rw [List.length_take, List.length_drop, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb2
      rw [hr'] at h
      exact hout x hx r' h

/-- **`ZPP = RP ∩ coRP`** ([AB09, Thm 7.8]).  Stated relative to the
efficiency notion `E`, under the closure properties the two directions use.

This is the identity for the **Las Vegas / abort-form** `ZPP` (`InZPP`: a
zero-error verifier that outputs `some b` or aborts with `none`, abort
probability `≤ 1/2`), **not** the book's expected-polynomial-time formulation
([AB09, Def 7.7]).  The two are equivalent by the standard truncate-and-repeat
bridge, which is not formalized here; until it is, read this as the abort-form
identity (the documented deviation, plan question CH7-Q2).

**Proof sketch.** (⊆) A zero-error verifier yields an `RP` verifier by
answering `true` exactly on output `some true` (`hAns`): inputs outside `L`
are never accepted (zero error), and inputs in `L` are accepted whenever the
verifier does not abort, hence with probability at least `1/2`.  Amplify
`1/2` to `2/3` with a 2-fold `OR` (`anyVerifier`, `hAny`): soundness is
preserved (an `OR` of never-accepting runs never accepts) and the failure
probability drops to `(1/2)² = 1/4`, so success is `≥ 3/4 ≥ 2/3`.  (A strict
*majority* cannot amplify success probability exactly `1/2`, which is why
the one-sided `OR` closure is the right tool here.)  Symmetrically with
`some false` for `Lᶜ`, giving `coRP`.  (⊇) Race an `RP` verifier `M₁` for
`L` against an `RP` verifier `M₂` for `Lᶜ` on split randomness
(`raceVerifier`): a definite answer is never wrong, since `M₁` accepting
certifies `x ∈ L` and `M₂` accepting certifies `x ∉ L`; and whichever of the
two is the "live" verifier for `x` accepts with probability ≥ `2/3`, so the
race aborts with probability at most `1/3 ≤ 1/2`. -/
theorem inZPP_iff_inRP_and_inCoRP (hRace : ClosedUnderRace E)
    (hAns : ClosedUnderAnswerIs E) (hAny : ClosedUnderAny E)
    (L : Language Bool) :
    InZPP E L ↔ InRP E L ∧ InCoRP E L := by
  classical
  constructor
  · rintro ⟨M, a, k, hM, hprop⟩
    constructor
    · refine inRP_of_zeroError E hAns hAny hM L true
        (fun x hx => ⟨?_, (hprop x).2.2⟩) (fun x hx => (hprop x).2.1 hx)
      simpa using (hprop x).1 hx
    · refine inRP_of_zeroError E hAns hAny hM Lᶜ false
        (fun x hx => ⟨?_, (hprop x).2.2⟩)
        (fun x hx => (hprop x).1 (Set.not_notMem.mp hx))
      simpa using (hprop x).2.1 hx
  · rintro ⟨⟨M₁, a₁, k₁, hM₁, h₁⟩, M₂, a₂, k₂, hM₂, h₂⟩
    -- Trim `M₂` to its first `polyLen a₂ k₂` bits, then race.
    set M₂' : List Bool → List Bool → Bool :=
      anyVerifier M₂ (polyLen a₂ k₂) (polyLen 1 0) with hM₂'def
    have hM₂'eff : E.Eff (boolVerifier M₂') := hAny M₂ a₂ k₂ 1 0 hM₂
    have hM₂'eq : ∀ (x : List Bool) (w : List Bool),
        M₂' x w = M₂ x (w.take (polyLen a₂ k₂ x.length)) := by
      intro x w
      show (List.range (polyLen 1 0 x.length)).any _ = _
      rw [show polyLen 1 0 x.length = 1 by simp [polyLen]]
      show (List.range 1).any _ = _
      rw [show List.range 1 = [0] from rfl]
      simp [List.any_cons]
    refine ⟨raceVerifier M₁ M₂' (polyLen a₁ k₁), a₁ + a₂, k₁ + k₂,
      hRace M₁ M₂' a₁ k₁ hM₁ hM₂'eff, fun x => ?_⟩
    set n := x.length
    set q₁ := polyLen a₁ k₁ n with hq₁
    set q₂ := polyLen a₂ k₂ n with hq₂
    set Q := polyLen (a₁ + a₂) (k₁ + k₂) n with hQ
    have hone : 1 ≤ n + 1 := Nat.le_add_left 1 n
    have hQ₁ : q₁ ≤ Q := by
      rw [hq₁, hQ]
      unfold polyLen
      calc a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
        _ ≤ (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_right _ (by omega)
    have hQ₂ : q₁ + q₂ ≤ Q := by
      rw [hq₁, hq₂, hQ]
      unfold polyLen
      have e₁ : a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      have e₂ : a₂ * (n + 1) ^ k₂ ≤ a₂ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      calc a₁ * (n + 1) ^ k₁ + a₂ * (n + 1) ^ k₂
          ≤ a₁ * (n + 1) ^ (k₁ + k₂) + a₂ * (n + 1) ^ (k₁ + k₂) := by omega
        _ = (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) := by ring
    -- Lengths of the two segments fed to the verifiers.
    have hlen₁ : ∀ rr : Fin Q → Bool, ((List.ofFn rr).take q₁).length = q₁ := by
      intro rr
      simp [List.length_take, List.length_ofFn]
      omega
    have hlen₂ : ∀ rr : Fin Q → Bool,
        (((List.ofFn rr).drop q₁).take q₂).length = q₂ := by
      intro rr
      simp [List.length_take, List.length_drop, List.length_ofFn]
      omega
    -- The three branches of the race on a concrete random string.
    have hrace_val : ∀ rr : Fin Q → Bool,
        raceVerifier M₁ M₂' (polyLen a₁ k₁) x (List.ofFn rr) =
          if M₁ x ((List.ofFn rr).take q₁) then some true
          else if M₂ x (((List.ofFn rr).drop q₁).take q₂) then some false
          else none := by
      intro rr
      show (if M₁ x ((List.ofFn rr).take q₁) then some true
        else if M₂' x ((List.ofFn rr).drop q₁) then some false else none) = _
      rw [hM₂'eq]
    refine ⟨fun hx rr => ?_, fun hx rr => ?_, ?_⟩
    · -- `x ∈ L`: never answers `some false`
      rw [hrace_val rr]
      have hx' : x ∉ Lᶜ := Set.not_notMem.mpr hx
      obtain ⟨r₂, hr₂⟩ := exists_ofFn_eq (hlen₂ rr)
      have hM₂false : M₂ x (((List.ofFn rr).drop q₁).take q₂) = false := by
        rw [hr₂]
        exact (h₂ x).2 hx' r₂
      rw [hM₂false]
      split
      · simp
      · simp
    · -- `x ∉ L`: never answers `some true`
      rw [hrace_val rr]
      obtain ⟨r₁, hr₁⟩ := exists_ofFn_eq (hlen₁ rr)
      have hM₁false : M₁ x ((List.ofFn rr).take q₁) = false := by
        rw [hr₁]
        exact (h₁ x).2 hx r₁
      rw [hM₁false]
      split
      · simp_all
      · split <;> simp
    · -- aborts with probability at most `1/2`
      obtain ⟨m₂, hm₂⟩ : ∃ m₂, Q = q₁ + m₂ := ⟨Q - q₁, by omega⟩
      have hq₂m₂ : q₂ ≤ m₂ := by omega
      have hs1 : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb Q (fun l => (fun l' => ¬ (M₁ x l' = true)) (l.take q₁) ∧
            (fun w => ¬ (M₂ x (w.take q₂) = true)) (l.drop q₁)) :=
        randProb_congr fun rr => by
          rw [hrace_val rr]
          rcases hb₁ : M₁ x ((List.ofFn rr).take q₁) <;>
            rcases hb₂ : M₂ x (((List.ofFn rr).drop q₁).take q₂) <;> simp_all
      have hs3 := randProb_split q₁ m₂ (fun l' => ¬ (M₁ x l' = true))
        (fun w => ¬ (M₂ x (w.take q₂) = true))
      have hs4 := randProb_take hq₂m₂ (fun l' => ¬ (M₂ x l' = true))
      have hnone_eq : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb q₁ (fun l => ¬ (M₁ x l = true)) *
            randProb q₂ (fun l => ¬ (M₂ x l = true)) := by
        rw [hs1, hm₂, hs3, hs4]
      rw [hnone_eq]
      by_cases hx : x ∈ L
      · have hacc := (h₁ x).1 hx
        have h1 : randProb q₁ (fun l => ¬ (M₁ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ (1/3) * 1 := by
              refine mul_le_mul h1 randProb_le_one randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num
      · have hacc := (h₂ x).1 hx
        have h2 : randProb q₂ (fun l => ¬ (M₂ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ 1 * (1/3) := by
              refine mul_le_mul randProb_le_one h2 randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num

/-- The advantage demanded of a weak `BPP` verifier on inputs of length `n`:
`min (1/6) ((n+1)^{-c})`.  For `c ≥ 1` and `n ≥ 5` this is the book's
`n^{-c}` up to the `n+1` shift (for `c = 0` both the book's `n^{-c}` and
`(n+1)^{-c}` are the constant `1`, and the cap takes over); the cap `1/6`
keeps the threshold `1/2 + weakAdv c n ≤ 2/3` attainable at small lengths,
where the book's literal `1/2 + n^{-c}` exceeds `1` (see the module
docstring's **Deviations**). -/
def weakAdv (c n : ℕ) : ℚ :=
  min (1/6) (((n : ℚ) + 1)⁻¹ ^ c)

theorem weakAdv_pos (c n : ℕ) : 0 < weakAdv c n := by
  unfold weakAdv
  refine lt_min (by norm_num) ?_
  positivity

theorem weakAdv_le_sixth (c n : ℕ) : weakAdv c n ≤ 1/6 :=
  min_le_left _ _

theorem weakAdv_ge (c n : ℕ) :
    (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ weakAdv c n := by
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hy1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [inv_le_one₀ (by positivity)]
    have := Nat.cast_nonneg (α := ℚ) n
    linarith
  unfold weakAdv
  exact le_min (by linarith) (by linarith)

/-- The arithmetic core of the amplification: with
`k(n) = 56·(n+1)^{2c+d}` repetitions, the elementary tail bound beats
`2^{-((n+1)^d + 1)}`. -/
theorem weakAdv_tail_bound (c d n : ℕ) :
    2 * (1 - 4 * weakAdv c n ^ 2) ^ (polyLen 56 (2 * c + d) n / 2) ≤
      (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  have hε6 : weakAdv c n ≤ 1/6 := weakAdv_le_sixth c n
  set ε := weakAdv c n with hε
  have hx1 : 4 * ε ^ 2 ≤ 1 := by nlinarith
  have hx0 : (0:ℚ) ≤ 4 * ε ^ 2 := by positivity
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hc0 : (0:ℚ) ≤ ((n : ℚ) + 1) ^ c := by positivity
  have hcancel : ((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  have hεge : (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ ε := weakAdv_ge c n
  have hm : 1 ≤ ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ) * (4 * ε ^ 2) := by
    have hcast : ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ)
        = 9 * ((n : ℚ) + 1) ^ (2 * c) := by
      push_cast
      ring
    rw [hcast]
    have h1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 6 * ε := by linarith
    have h2 : (((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c
        ≤ (6 * ε) * (6 * ε) := mul_self_le_mul_self hy0 h1
    have h3 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) = 1 := by
      rw [two_mul, pow_add]
      calc ((n : ℚ) + 1) ^ c * ((n : ℚ) + 1) ^ c *
            ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
          = (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) *
            (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) := by ring
        _ = 1 := by rw [hcancel, one_mul]
    have h4 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
        ≤ ((n : ℚ) + 1) ^ (2 * c) * ((6 * ε) * (6 * ε)) := by
      refine mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [h3, h4]
  have hexp : (9 * (n + 1) ^ (2 * c)) * ((n + 1) ^ d + 2) ≤
      polyLen 56 (2 * c + d) n / 2 := by
    have h562 : polyLen 56 (2 * c + d) n / 2 = 28 * (n + 1) ^ (2 * c + d) := by
      unfold polyLen
      omega
    rw [h562, pow_add]
    have hge1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hge2 : 1 ≤ (n + 1) ^ (2 * c) := Nat.one_le_pow _ _ (by omega)
    nlinarith [hge1, hge2]
  have hhalf := one_sub_pow_le_half_pow hx0 hx1 hm hexp
  calc 2 * (1 - 4 * ε ^ 2) ^ (polyLen 56 (2 * c + d) n / 2)
      ≤ 2 * (1/2 : ℚ) ^ ((n + 1) ^ d + 2) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
        rw [show (n + 1) ^ d + 2 = ((n + 1) ^ d + 1) + 1 from rfl, pow_succ]
        ring

/-- `L ∈ BPP_{n^{-c}}`: like `InBPP`, but with success probability only
`1/2 + weakAdv c |x|`, i.e. an inverse-polynomial advantage over guessing.
[AB09, Lem 7.9], with the small-length repair described in the module
docstring. -/
def InBPPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ BPP` with error at most `2^{-((|x|+1)^d + 1)}` — the amplified form
produced by error reduction.  The exponent `(|x|+1)^d + 1 ≥ |x|^d`
strengthens [AB09, Thm 7.10]'s `2^{-|x|^d}` uniformly in `|x|`, and the
`+ 1` keeps the success threshold at least `3/4 > 2/3` at *every* length
and every `d` (including `d = 0` and the empty input), so
`InBPPStrong E d L → InBPP E L` follows directly using the same witnesses
(via the arithmetic inequality `2/3 ≤ 1 − (1/2)^{(n+1)^d + 1}`), with no closure
assumption on `E`.  (With the bare exponent `(|x|+1)^d`, a fair coin would
satisfy the definition at `d = 0` for every language, and at `|x| = 0` for
every `d` — a finite exception that cannot be patched for an abstract
model.) -/
def InBPPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- **Error reduction** ([AB09, Thm 7.10]).  A language decidable with an
inverse-polynomial advantage is decidable with success probability
`1 − 2^{-((|x|+1)^d + 1)}`, for every constant `d` — relative to `E`,
assuming `E` is closed under polynomial majority repetition.

**Proof.** Run the weak verifier `k(n) = 56·(n+1)^{2c+d}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  The vote count is binomially distributed
(`randProb_blockCount`), and the elementary tail estimate
`randProb_tail_le` bounds the error by `2·(1 − 4ε²)^{⌊k/2⌋}` with
`ε = weakAdv c n ≥ (n+1)^{-c}/6`; the rational Bernoulli bound
`one_sub_pow_le_half_pow` then gives `≤ 2^{-((n+1)^d + 1)}`
(`weakAdv_tail_bound`).  (The book computes with `e^{−2ε²k}`; the
elementary `(4p(1−p))^{k/2}` bound proves the same statement while keeping
every quantity rational.) -/
theorem bpp_error_reduction (hMaj : ClosedUnderMajority E) {c : ℕ}
    {L : Language Bool} (hL : InBPPWeak E c L) (d : ℕ) :
    InBPPStrong E d L := by
  classical
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)),
    56 * a, 2 * c + d + k, hMaj M a k 56 (2 * c + d) hM, fun x => ?_⟩
  have hqK : polyLen (56 * a) (2 * c + d + k) x.length
      = polyLen 56 (2 * c + d) x.length * polyLen a k x.length := by
    unfold polyLen
    ring
  set n := x.length with hn
  set q := polyLen a k n with hq
  set K := polyLen 56 (2 * c + d) n with hK
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  -- The majority verifier accepts iff more than half the blocks accept.
  have hmaj_iff : ∀ l : List Bool,
      majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)) x l = true ↔
        K < 2 * blockCount q K (M x) l := by
    intro l
    show decide (K < 2 * blockCount q K (M x) l) = true ↔ _
    rw [decide_eq_true_iff]
  -- Complementary vote counts.
  have hcount : ∀ l : List Bool,
      blockCount q K (M x) l +
        blockCount q K (fun l' => !(M x l')) l = K := by
    intro l
    unfold blockCount
    have haux : ∀ (p : ℕ → Bool) (li : List ℕ),
        li.countP p + li.countP (fun i => !(p i)) = li.length := by
      intro p li
      induction li with
      | nil => simp
      | cons hd tl ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        rcases hp : p hd <;> simp [hp] <;> omega
    rw [haux (fun i => M x ((l.drop (i * q)).take q)) (List.range K)]
    exact List.length_range
  -- Single-run probabilities.
  have hs_false : randProb q (fun l => M x l = false)
      = 1 - randProb q (fun l => M x l = true) := randProb_bool_false (M x)
  have hs_not : randProb q (fun l => (!(M x l)) = true)
      = randProb q (fun l => M x l = false) :=
    randProb_congr fun r => by simp
  rw [hqK]
  constructor
  · -- `x ∈ L`: the failure event is `K ≤ 2·(false votes)`
    intro hx
    have hW := (hprop x).1 hx
    have hsf : randProb q (fun l => (!(M x l)) = true) ≤ 1/2 - weakAdv c n := by
      rw [hs_not, hs_false]
      linarith
    have htail := randProb_tail_le q K (fun l' => !(M x l')) hε0.le hsf
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = true))
        = randProb (K * q) (fun l =>
            K ≤ 2 * blockCount q K (fun l' => !(M x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj_iff]
        have := hcount (List.ofFn r)
        constructor
        · intro h
          omega
        · intro h
          omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = true)
    have hbound := weakAdv_tail_bound c d n
    rw [hev] at hnot
    have : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (fun l' => !(M x l')) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith
  · -- `x ∉ L`: the failure event is `K < 2·(true votes)`
    intro hx
    have hW := (hprop x).2 hx
    have hst : randProb q (fun l => M x l = true) ≤ 1/2 - weakAdv c n := by
      have := hs_false
      linarith
    have htail := randProb_tail_le q K (M x) hε0.le hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = false))
        ≤ randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r) = true := by
        rcases hb : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r)
        · exact absurd hb hr
        · rfl
      have h2 := (hmaj_iff (List.ofFn r)).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = false)
    have hbound := weakAdv_tail_bound c d n
    have : randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith

/-- The amplified form implies plain `BPP` membership: the success
threshold `1 − 2^{-((|x|+1)^d+1)}` is at least `3/4 ≥ 2/3` at every length,
using the same witnesses. -/
theorem InBPPStrong.toInBPP {d : ℕ} {L : Language Bool}
    (hL : InBPPStrong E d L) : InBPP E L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨M, a, k, hM, fun x => ?_⟩
  have he : 2 ≤ (x.length + 1) ^ d + 1 := by
    have := Nat.one_le_pow d (x.length + 1) (by omega)
    omega
  have hth : (2/3 : ℚ) ≤ 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) := by
    have h2 : (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤ (1/2 : ℚ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he
    norm_num at h2
    linarith
  exact ⟨fun hx => hth.trans ((hprop x).1 hx),
    fun hx => hth.trans ((hprop x).2 hx)⟩

/-- **`BPP_{n^{-c}} = BPP`** ([AB09, Lem 7.9]): the success threshold `2/3`
in the definition of `BPP` can be weakened to an inverse-polynomial advantage
over `1/2` without changing the class.

**Proof.** `BPP ⊆ BPP_{n^{-c}}` since `weakAdv c n ≤ 1/6` makes the
weak threshold at most `2/3` at every length.  Conversely, error reduction
at `d = 0` (`bpp_error_reduction`) amplifies the weak advantage to success
probability `1 − (1/2)^{(n+1)^0+1} ≥ 3/4 ≥ 2/3`
(`InBPPStrong.toInBPP`). -/
theorem inBPPWeak_iff_inBPP (hMaj : ClosedUnderMajority E) (c : ℕ)
    (L : Language Bool) :
    InBPPWeak E c L ↔ InBPP E L := by
  constructor
  · intro hL
    exact (bpp_error_reduction E hMaj hL 0).toInBPP
  · rintro ⟨M, a, k, hM, hprop⟩
    refine ⟨M, a, k, hM, fun x => ?_⟩
    have hadv : 1/2 + weakAdv c x.length ≤ 2/3 := by
      have := weakAdv_le_sixth c x.length
      linarith
    exact ⟨fun hx => hadv.trans ((hprop x).1 hx),
      fun hx => hadv.trans ((hprop x).2 hx)⟩

end Randomized
