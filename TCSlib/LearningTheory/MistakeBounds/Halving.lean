/-
Copyright (c) 2026 Arhaan Aggarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arhaan Aggarwal
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Halving Algorithm and Its Optimal Mistake Bound

The Halving algorithm keeps a version space of hypotheses consistent with the examples seen
so far, predicts by majority vote, and discards every hypothesis that voted for the wrong
label. Each mistake therefore at least halves the version space, so in the realizable
setting (the target hypothesis lies in the finite class `H`) the algorithm makes at most
`log₂ |H|` mistakes [MRT18, Thm 8.1].

## Main definitions

- `Halving.voteFor`: The hypotheses in the version space that vote for a given label on an
  input.
- `Halving.predict`: The Halving prediction (majority vote, ties broken towards `true`).
- `Halving.update`: The version-space update after observing a labelled example.
- `Halving.mistakes`: The number of mistakes the Halving Algorithm makes on a finite list of
  inputs.

## Main results

- `Halving.voteFor_false_add_true`: The false-voters and true-voters partition the current
  version space.
- `Halving.update_subset`: A version-space update is a subset of the old version space.
- `Halving.target_mem_update`: In the realizable setting, the target hypothesis survives
  every update.
- `Halving.mistake_halves`: Every mistake leaves at most half the hypotheses.
- `Halving.log_succ_le_log_of_double_le`: If `b` is positive and `2*b ≤ a`, then
  `log₂ b + 1 ≤ log₂ a`.
- `Halving.mistakes_bound`: In the realizable setting, the Halving Algorithm makes at most
  `log₂ |V|` mistakes.
- `Halving.halving_bound`: The mistake bound starting from the initial finite hypothesis
  class `H`.

## References

* [MRT18] M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*,
  2nd ed., MIT Press, 2018.
* [Lit88] N. Littlestone, "Learning quickly when irrelevant attributes abound: A new
  linear-threshold algorithm", *Machine Learning* 2:285–318, 1988.

Original formalization by Arhaan Aggarwal.
-/

namespace Halving

variable {Hyp X : Type*}

/-- The set of hypotheses in the version space `V` whose evaluation on the input `x` equals
the label `y`, i.e. the hypotheses that vote for `y` on `x`.
[MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def voteFor (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    Finset Hyp :=
  V.filter (fun h => eval h x = y)

/-- The Halving prediction on the input `x`: the label that receives the majority of the
votes of the version space `V`, with ties broken towards `true`.
[MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def predict (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) : Bool :=
  if (voteFor eval V x true).card ≥ (voteFor eval V x false).card then
    true
  else
    false

/-- The version space after observing the labelled example `(x, y)`: the hypotheses of `V`
that agree with the label `y` on `x`; every hypothesis that voted for the other label is
discarded. [MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def update (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    Finset Hyp :=
  voteFor eval V x y

/-- The number of hypotheses of `V` voting `false` on `x` plus the number voting `true` on
`x` equals the size of `V`: the two vote sets partition the current version space. -/
lemma voteFor_false_add_true
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) :
    (voteFor eval V x false).card + (voteFor eval V x true).card = V.card := by
  unfold voteFor
  have hfilter :
      V.filter (fun h : Hyp => eval h x = true) =
        V.filter (fun h : Hyp => ¬ eval h x = false) := by
    ext h
    cases eval h x <;> simp
  rw [hfilter]
  exact Finset.filter_card_add_filter_neg_card_eq_card
    (s := V) (p := fun h : Hyp => eval h x = false)

/-- Updating the version space on a labelled example only removes hypotheses: the updated
version space `update eval V x y` is a subset of the old version space `V`. -/
lemma update_subset
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    update eval V x y ⊆ V := by
  intro h hh
  have hh' : h ∈ V ∧ eval h x = y := by
    simpa [update, voteFor] using hh
  exact hh'.1

/-- In the realizable setting the target hypothesis survives every update: if `target` lies
in `V`, then it lies in the version space obtained by updating `V` on `x` with the label
that `target` itself assigns to `x`. -/
lemma target_mem_update
    (eval : Hyp → X → Bool) (target : Hyp) (V : Finset Hyp) (x : X)
    (htarget : target ∈ V) :
    target ∈ update eval V x (eval target x) := by
  simp [update, voteFor, htarget]

/-- Every mistake at least halves the version space: if the Halving prediction on `x`
differs from the observed label `y`, then the version space updated on `(x, y)` has at most
half as many hypotheses as `V`, i.e. `2 · |update eval V x y| ≤ |V|`.
[MRT18, proof of Thm 8.1].

**Proof sketch.** Case on the label `y`. If the prediction was wrong, the majority (ties
included) voted for the other label, so the voters for `y` are at most the voters against
`y`. Since the two vote sets partition `V` (`voteFor_false_add_true`), the survivors number
at most half of `V`. -/
lemma mistake_halves
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool)
    (hmistake : predict eval V x ≠ y) :
    2 * (update eval V x y).card ≤ V.card := by
  cases y
  · -- true label is false/0, so a mistake means the algorithm predicted true/1.
    unfold predict at hmistake
    by_cases hmaj :
        (voteFor eval V x true).card ≥ (voteFor eval V x false).card
    · have hsum := voteFor_false_add_true (eval := eval) (V := V) (x := x)
      simp [update, hmaj] at hmistake ⊢
      omega
    · simp [hmaj] at hmistake
  · -- true label is true/1, so a mistake means the algorithm predicted false/0.
    unfold predict at hmistake
    by_cases hmaj :
        (voteFor eval V x true).card ≥ (voteFor eval V x false).card
    · simp [hmaj] at hmistake
    · have hsum := voteFor_false_add_true (eval := eval) (V := V) (x := x)
      have hle :
          (voteFor eval V x true).card ≤
            (voteFor eval V x false).card := by
        omega
      simp [update, hmaj] at hmistake ⊢
      omega

/-- If `b` is positive and `2 · b ≤ a`, then `⌊log₂ b⌋ + 1 ≤ ⌊log₂ a⌋` (floors of base-2
logarithms, as computed by `Nat.log`): doubling spends exactly one unit of logarithmic
budget. Arithmetic glue for `mistakes_bound`, with no textbook counterpart. -/
lemma log_succ_le_log_of_double_le {a b : ℕ}
    (hb : 0 < b) (hhalve : 2 * b ≤ a) :
    Nat.log 2 b + 1 ≤ Nat.log 2 a := by
  have hbne : b ≠ 0 := by omega
  have hpowlog : 2 ^ Nat.log 2 b ≤ b :=
    Nat.pow_log_le_self 2 hbne
  have hpow : 2 ^ (Nat.log 2 b + 1) ≤ a := by
    calc
      2 ^ (Nat.log 2 b + 1)
          = 2 ^ Nat.log 2 b * 2 := by
              rw [pow_succ]
      _ ≤ b * 2 := Nat.mul_le_mul_right 2 hpowlog
      _ = 2 * b := by omega
      _ ≤ a := hhalve
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow

/-- The number of mistakes the Halving Algorithm makes when run from the version space `V`
over the finite list of inputs `xs`, with every label generated by the hypothesis `target`
(the label of `x` is `eval target x`). At each input the algorithm predicts with the current
version space, incurs one mistake if that prediction differs from the target's label, and
then updates the version space with the observed label before moving to the next input.
[MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def mistakes (eval : Hyp → X → Bool) (target : Hyp) (V : Finset Hyp) :
    List X → ℕ
  | [] => 0
  | x :: xs =>
      let y := eval target x
      let V' := update eval V x y
      (if predict eval V x = y then 0 else 1) + mistakes eval target V' xs

/-- In the realizable setting, the Halving Algorithm makes at most `⌊log₂ |V|⌋` mistakes: if
the target hypothesis lies in the finite version space `V`, then on any finite list of
inputs `xs`, labelled by `target`, the number of mistakes is at most `Nat.log 2 V.card`.
[MRT18, Thm 8.1]; origin [Lit88, §3].
Deviation: the bound is stated as `Nat.log 2 V.card` (the floor of `log₂ |V|`) over an
explicit finite list of examples with an explicit realizable target `target ∈ V`; the
source's `opt(H) ≤ log₂ |H|` is the same bound for the adversarial online model.

**Proof sketch.** Induction on the list of inputs, generalizing the version space `V`. The
empty list makes no mistakes. For an input `x` followed by `xs`, let `y` be the target's
label on `x` and `V'` the version space updated on `(x, y)`.
Step 1: the target survives the update (`target ∈ V'`), so the induction hypothesis applies
to `V'` and bounds the mistakes on `xs` by `⌊log₂ |V'|⌋`.
Step 2 (no mistake on `x`): `V' ⊆ V`, so `|V'| ≤ |V|` and, by monotonicity of `Nat.log`,
`⌊log₂ |V'|⌋ ≤ ⌊log₂ |V|⌋`; the mistake count on `x :: xs` equals that on `xs`.
Step 3 (mistake on `x`): by the halving lemma `2 · |V'| ≤ |V|`, and `V'` is nonempty because
it contains the target, so `⌊log₂ |V'|⌋ + 1 ≤ ⌊log₂ |V|⌋`; the one mistake on `x` is paid by
this unit of logarithmic budget. -/
theorem mistakes_bound
    (eval : Hyp → X → Bool) (target : Hyp) (V : Finset Hyp) (xs : List X)
    (htarget : target ∈ V) :
    mistakes eval target V xs ≤ Nat.log 2 V.card := by
  induction xs generalizing V with
  | nil =>
      simp [mistakes]
  | cons x xs ih =>
      let y := eval target x
      let V' := update eval V x y
      -- Step 1: the target survives the update, so the induction hypothesis applies to `V'`.
      have htarget' : target ∈ V' := by
        simpa [V', y] using target_mem_update eval target V x htarget
      have ih' : mistakes eval target V' xs ≤ Nat.log 2 V'.card :=
        ih V' htarget'
      by_cases hcorr : predict eval V x = y
      · -- No mistake: the version space can only shrink.
        -- Step 2: `V' ⊆ V`, hence `|V'| ≤ |V|` and the log bound is monotone.
        have hsubset : V' ⊆ V := by
          simpa [V', y] using update_subset eval V x y
        have hcard : V'.card ≤ V.card := Finset.card_le_card hsubset
        have hlog : Nat.log 2 V'.card ≤ Nat.log 2 V.card :=
          Nat.log_mono_right hcard
        calc
          mistakes eval target V (x :: xs)
              = mistakes eval target V' xs := by
                  simp [mistakes, y, V', hcorr]
          _ ≤ Nat.log 2 V'.card := ih'
          _ ≤ Nat.log 2 V.card := hlog
      · -- Mistake: apply the halving lemma and spend one unit of logarithmic budget.
        -- Step 3: `2·|V'| ≤ |V|` and `V'` is nonempty, so `⌊log₂ |V'|⌋ + 1 ≤ ⌊log₂ |V|⌋`.
        have hhalve : 2 * V'.card ≤ V.card := by
          simpa [V', y] using mistake_halves eval V x y hcorr
        have hpos : 0 < V'.card := by
          exact Finset.card_pos.mpr ⟨target, htarget'⟩
        have hlogstep : Nat.log 2 V'.card + 1 ≤ Nat.log 2 V.card :=
          log_succ_le_log_of_double_le hpos hhalve
        calc
          mistakes eval target V (x :: xs)
              = 1 + mistakes eval target V' xs := by
                  simp [mistakes, y, V', hcorr]
          _ ≤ 1 + Nat.log 2 V'.card := Nat.add_le_add_left ih' 1
          _ = Nat.log 2 V'.card + 1 := by omega
          _ ≤ Nat.log 2 V.card := hlogstep

/-- The Halving mistake bound from the initial finite hypothesis class `H`: in the realizable
setting (`target ∈ H`), the Halving Algorithm makes at most `⌊log₂ |H|⌋` mistakes on any
finite list of inputs labelled by `target`. This is `mistakes_bound` with `V := H`.
[MRT18, Thm 8.1]; origin [Lit88, §3].
Deviation: `Nat.log 2 H.card` (floor of `log₂ |H|`) over an explicit finite example list
with an explicit realizable target, versus the source's `opt(H) ≤ log₂ |H|` for the
adversarial online model. -/
theorem halving_bound
    (eval : Hyp → X → Bool) (target : Hyp) (H : Finset Hyp) (xs : List X)
    (htarget : target ∈ H) :
    mistakes eval target H xs ≤ Nat.log 2 H.card :=
  mistakes_bound eval target H xs htarget

end Halving
