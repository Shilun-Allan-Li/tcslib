/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import TCSlib.CommunicationComplexity.DeterministicCC.OneWay
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import TCSlib.CommunicationComplexity.DeterministicCC.Hamming
import TCSlib.CommunicationComplexity.DeterministicCC.Helper
import TCSlib.CommunicationComplexity.NewmanTheorem.OneWayMinimax
import Mathlib.Probability.UniformOn
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Semifield

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Indexing

## Main results

- `Functions.Indexing.le_oneWayCommunicationComplexity`: One-way CC lower bound `n` for the indexing function via distributional argument

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/


namespace CommunicationComplexity

namespace Functions.Indexing

open Deterministic
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable (n : ℕ+)

/-- The indexing function: Bob outputs Alice's `i`-th bit. -/
def indexing (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i

/-- The trivial one-way protocol for indexing: Alice sends her full string. -/
def trivialProtocol : OneWay.Protocol (Fin n → Bool) (Fin n) Bool where
  Message := Fin n → Bool
  send := id
  decode := fun x i => x i

/-- One-way upper bound for indexing: Alice can send all `n` bits. -/
theorem oneWayCommunicationComplexity_le :
    OneWay.communicationComplexity (indexing n) ≤ (n : ℕ) := by
  rw [OneWay.communicationComplexity_le_iff]
  refine ⟨trivialProtocol n, (by ext x i; rfl), ?_⟩
  · simp [trivialProtocol, OneWay.Protocol.cost,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow]

/-- Deterministic upper bound for indexing: Bob can send his index and then
Alice can send the output bit. -/
theorem communicationComplexity_le :
    Deterministic.communicationComplexity (indexing n) ≤ Nat.clog 2 (n : ℕ) + 1 := by
  have hbool : Nat.clog 2 2 = 1 := by decide
  calc
    Deterministic.communicationComplexity (indexing n)
      ≤ Nat.clog 2 (Nat.card (Fin n)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_Y_alpha (indexing n)
    _ = Nat.clog 2 (n : ℕ) + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
        rw [hbool]
        norm_cast

/-- One-way lower bound for indexing: any correct deterministic one-way protocol
must send at least `n` bits. -/
theorem le_oneWayCommunicationComplexity : n ≤ OneWay.communicationComplexity (indexing n) := by
  rw [OneWay.le_communicationComplexity_iff]
  intro p hp_comp
  have hinj : Function.Injective p.send := by
    intro x y heq
    ext i
    have hx := congrFun (congrFun hp_comp x) i
    have hy := congrFun (congrFun hp_comp y) i
    have hm : p.decode (p.send x) i = p.decode (p.send y) i := by
      simpa using congrArg (fun m => p.decode m i) heq
    simpa [OneWay.Protocol.Computes, OneWay.Protocol.run, indexing] using
      hx.symm.trans (hm.trans hy)
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card p.Message := by
    exact Fintype.card_le_of_injective p.send hinj
  have hpow_dom : 2 ^ (n : ℕ) ≤ Fintype.card p.Message := by
    simpa [Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] using hcard
  have hcost : Fintype.card p.Message ≤ 2 ^ p.cost := by
    apply Nat.le_pow_clog; linarith
  by_contra!
  have h_bad : 2 ^ p.cost < 2 ^ (n : ℕ) := by
    refine Nat.pow_lt_pow_of_lt (by linarith) this
  omega

theorem oneWayCommunicationComplexity_eq :
    OneWay.communicationComplexity (indexing n) = (n : ℕ) := by
  exact le_antisymm (oneWayCommunicationComplexity_le n) (le_oneWayCommunicationComplexity n)

/-- Coercion helper showing `(n : ℕ)` is nonzero for `n : ℕ+`. -/
instance indexNeZero : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.pos⟩

/-- Uniform measure-space structure on `Fin n`. -/
noncomputable instance indexMeasureSpace :
    MeasureSpace (Fin n) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

/-- Uniform measure on `Fin n` is a probability measure. -/
noncomputable instance indexIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (Fin n)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

/-- Finite probability-space packaging for uniform `Fin n`. -/
noncomputable instance indexFiniteProbabilitySpace :
    FiniteProbabilitySpace (Fin n) :=
  FiniteProbabilitySpace.of (Fin n)

/-- Finite probability-space packaging for uniform `BoolInput n`. -/
noncomputable instance boolInputFiniteProbabilitySpace :
    FiniteProbabilitySpace (BoolInput n) := by
  change FiniteProbabilitySpace (CoinTape n)
  infer_instance

/-- Uniform distribution on indexing inputs `(x, i)`, where `x` and `i`
are chosen independently and uniformly. -/
noncomputable def indexingInputDist :
    FiniteProbabilitySpace (BoolInput n × Fin n) := by
  letI : MeasureSpace (BoolInput n × Fin n) :=
    ⟨ProbabilityTheory.uniformOn Set.univ⟩
  letI : IsProbabilityMeasure (volume : Measure (BoolInput n × Fin n)) := by
    change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
    infer_instance
  exact FiniteProbabilitySpace.of (BoolInput n × Fin n)

open Classical in
/-- Bob's full answer vector for a fixed received one-way message. -/
private def answerVector
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (m : p.Message) : BoolInput n :=
  fun i => p.decode m i

open Classical in
/-- The finite set of answer vectors realizable by protocol messages. -/
private def answerSet
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) : Finset (BoolInput n) :=
  Finset.image (answerVector (n := n) p) Finset.univ

open Classical in
/-- Inputs `x` that are not within Hamming radius `n/4` of any realizable answer vector. -/
private def badInput
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) : Prop :=
  ¬ ∃ a ∈ answerSet (n := n) p, (hammingDist x a : ℝ) < (n : ℝ) / 4

open Classical in
/-- Decidability of the `badInput` predicate (finite ambient types). -/
private noncomputable instance badInputDecidablePred
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    DecidablePred (badInput (n := n) p) := by
  infer_instance

open Classical in
/-- Indices where protocol `p` errs on fixed input string `x`. -/
private def mismatchSubtype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) : Type :=
  {i : Fin n // p.run x i ≠ indexing n x i}

open Classical in
/-- Finiteness of mismatch coordinates for fixed `x`. -/
private noncomputable instance mismatchSubtypeFintype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) :
    Fintype (mismatchSubtype (n := n) p x) := by
  unfold mismatchSubtype
  infer_instance

open Classical in
/-- Input pairs `(x, i)` where protocol `p` is incorrect. -/
private def badPairSubtype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) : Type :=
  {xi : BoolInput n × Fin n // p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}

open Classical in
/-- Finiteness of incorrect input pairs. -/
private noncomputable instance badPairSubtypeFintype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    Fintype (badPairSubtype (n := n) p) := by
  unfold badPairSubtype
  infer_instance

open Classical in
/-- Equivalence between incorrect pairs and a sigma of per-`x` mismatch indices. -/
private def badPairEquivSigma
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    badPairSubtype (n := n) p ≃ Σ x : BoolInput n, mismatchSubtype (n := n) p x where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := by
    rcases z with ⟨⟨x, i⟩, hz⟩
    rfl
  right_inv z := by
    rcases z with ⟨x, ⟨i, hi⟩⟩
    rfl

/-- The mismatch count for fixed `x` is exactly a Hamming distance to the
answer vector induced by `p.send x`. -/
private lemma mismatchSubtype_card_eq_hammingDist
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) :
    Fintype.card (mismatchSubtype (n := n) p x) =
      hammingDist x (answerVector (n := n) p (p.send x)) := by
  classical
  unfold hammingDist
  simpa [mismatchSubtype, Deterministic.OneWay.Protocol.run, indexing, answerVector, ne_comm] using
    (Fintype.card_subtype (p := fun i : Fin n => p.decode (p.send x) i ≠ x i))

/-- Total incorrect-pair count equals the sum of per-`x` mismatch counts. -/
private lemma badPairSubtype_card_eq_sum
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    Fintype.card (badPairSubtype (n := n) p) =
      ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := by
  calc
    Fintype.card (badPairSubtype (n := n) p) =
        Fintype.card (Σ x : BoolInput n, mismatchSubtype (n := n) p x) := by
          exact Fintype.card_congr (badPairEquivSigma (n := n) p)
    _ = ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := Fintype.card_sigma

/-- Number of distinct answer vectors is at most `2 ^ p.cost`. -/
private lemma answerSet_card_le_pow_cost
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    (answerSet (n := n) p).card ≤ 2 ^ p.cost := by
  calc
    (answerSet (n := n) p).card
        ≤ Fintype.card p.Message := by
          simpa [answerSet] using
            (Finset.card_image_le (f := answerVector (n := n) p)
              (s := (Finset.univ : Finset p.Message)))
    _ ≤ 2 ^ p.cost := by
      exact Nat.le_pow_clog (by decide) _

/-- A bad input has Hamming distance at least `n/4` from its own induced answer vector. -/
private lemma badInput_implies_hammingDist_ge
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    {x : BoolInput n}
    (hx : badInput (n := n) p x) :
    (n : ℝ) / 4 ≤ hammingDist x (answerVector (n := n) p (p.send x)) := by
  have hmem : answerVector (n := n) p (p.send x) ∈ answerSet (n := n) p := by
    exact Finset.mem_image.mpr ⟨p.send x, Finset.mem_univ _, rfl⟩
  have hnot :
      ¬ (hammingDist x (answerVector (n := n) p (p.send x)) : ℝ) < (n : ℝ) / 4 := by
    intro hlt
    exact hx ⟨answerVector (n := n) p (p.send x), hmem, hlt⟩
  exact le_of_not_gt hnot

/-- Core counting step in the indexing distributional argument: if at least half
of Alice inputs are bad (in the answer-vector sense), then the deterministic one-way
protocol has distributional error at least `1/8` under the uniform input distribution. -/
theorem distributionalError_ge_one_eighth_of_bad_half
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (hbad :
      2 ^ ((n : ℕ) - 1) ≤
        (Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)).card) :
    p.distributionalError (μ := indexingInputDist n) (indexing n) ≥ (1 / 8 : ℝ) := by
  classical
  let bad : Finset (BoolInput n) :=
    Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)
  let g : BoolInput n → ℝ := fun x => Fintype.card (mismatchSubtype (n := n) p x)
  have hsplit :
      (∑ x : BoolInput n, g x) =
        (Finset.sum bad g) +
          (Finset.sum (Finset.univ.filter (fun x : BoolInput n => x ∉ bad)) g) := by
    simpa [bad] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun x : BoolInput n => x ∈ bad) (f := g)).symm
  have hsum_ge_bad : (∑ x : BoolInput n, g x) ≥ Finset.sum bad g := by
    have hnonneg :
        0 ≤ Finset.sum (Finset.univ.filter (fun x : BoolInput n => x ∉ bad)) g := by
      positivity
    linarith
  have hbad_term : ∀ x ∈ bad, (n : ℝ) / 4 ≤ g x := by
    intro x hx
    have hx_bad : badInput (n := n) p x := (Finset.mem_filter.mp hx).2
    have hdist := badInput_implies_hammingDist_ge (n := n) p hx_bad
    simpa [g, mismatchSubtype_card_eq_hammingDist] using hdist
  have hsum_bad_ge :
      Finset.sum bad g ≥ Finset.sum bad (fun _ => (n : ℝ) / 4) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact hbad_term x hx
  have hsum_bad_const :
      (Finset.sum bad (fun _ => (n : ℝ) / 4)) = (bad.card : ℝ) * ((n : ℝ) / 4) := by
    simp
  have hsum_ge :
      (∑ x : BoolInput n, g x) ≥ (bad.card : ℝ) * ((n : ℝ) / 4) := by
    linarith [hsum_ge_bad, hsum_bad_ge, hsum_bad_const]
  have hbad_real : ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) ≤ (bad.card : ℝ) := by
    exact_mod_cast hbad
  have hcard_badpair :
      (Fintype.card (badPairSubtype (n := n) p) : ℝ) ≥
        ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4) := by
    have hsum_card :
        (Fintype.card (badPairSubtype (n := n) p) : ℝ) = ∑ x : BoolInput n, g x := by
      simp [g, badPairSubtype_card_eq_sum]
    have hmult :
        (bad.card : ℝ) * ((n : ℝ) / 4) ≥
          ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4) := by
      gcongr
    linarith [hsum_ge, hsum_card, hmult]
  rw [Deterministic.OneWay.Protocol.distributionalError]
  change
    (((ProbabilityTheory.uniformOn Set.univ : Measure (BoolInput n × Fin n))
      {xi : BoolInput n × Fin n | p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}).toReal) ≥
      (1 / 8 : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_filter]
  let errSet : Set (BoolInput n × Fin n) :=
    {xi : BoolInput n × Fin n | p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}
  let errFinset : Finset (BoolInput n × Fin n) := {ω : BoolInput n × Fin n | ω ∈ errSet}
  have hcard_eq :
      errFinset.card =
        Fintype.card (badPairSubtype (n := n) p) := by
    simp [errFinset, errSet, badPairSubtype, Fintype.card_subtype]
  have hcard_eq_real :
      (errFinset.card : ℝ) =
        Fintype.card (badPairSubtype (n := n) p) := by
    exact_mod_cast hcard_eq
  have hcard_eq_div :
      ((errFinset.card : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) =
        ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) := by
    exact congrArg (fun t : ℝ => t / (Fintype.card (BoolInput n × Fin n) : ℝ)) hcard_eq_real
  have hden :
      (Fintype.card (BoolInput n × Fin n) : ℝ) = (2 ^ (n : ℕ) : ℝ) * (n : ℝ) := by
    simp [BoolInput, Fintype.card_prod, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos
  have hpow_pos : (0 : ℝ) < (2 ^ (n : ℕ) : ℝ) := by positivity
  have hmain :
      (Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ))
      ≥
        (((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4)) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ)) := by
    exact div_le_div_of_nonneg_right hcard_badpair (by positivity)
  have hfinal :
      (((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4)) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ)) = (1 / 8 : ℝ) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp n.pos) with ⟨m, hm⟩
    rw [hm, Nat.succ_sub_one, pow_succ]
    have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by
      exact_mod_cast (show (2 ^ m : ℕ) = 2 ^ m by rfl)
    rw [hcast]
    have hm_ne : ((m.succ : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hm_ne, pow_ne_zero]
    ring_nf
  have htarget_rhs :
      ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) ≥ (1 / 8 : ℝ) := by
    rw [hden]
    linarith [hmain, hfinal]
  have htarget_lhs :
      ((errFinset.card : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) ≥ (1 / 8 : ℝ) := by
    calc
      ((errFinset.card : ℝ) / (Fintype.card (BoolInput n × Fin n) : ℝ))
          = ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
              (Fintype.card (BoolInput n × Fin n) : ℝ)) := hcard_eq_div
      _ ≥ (1 / 8 : ℝ) := htarget_rhs
  convert htarget_lhs using 1
  refine congrArg (fun t : Finset (BoolInput n × Fin n) =>
      (t.card : ℝ) / (Fintype.card (BoolInput n × Fin n) : ℝ)) ?_
  ext x
  simp [errFinset, errSet]

/-! ### Counting lemmas for the distributional indexing lower bound -/

/-- For indices `i` strictly below `n/4`, the binomial coefficients grow by at least a factor
of `3`.
This is the quantitative step used to control the partial binomial sum up to `n/4`. -/
private lemma choose_three_mul_le_succ_choose_quarter
    {n i : ℕ} (hi : i < n / 4) :
    3 * Nat.choose n i ≤ Nat.choose n (i + 1) := by
  have hineq : 3 * (i + 1) ≤ n - i := by
    have hi' : i + 1 ≤ n / 4 := Nat.succ_le_of_lt hi
    have hmul : 4 * (i + 1) ≤ n := by
      exact (Nat.mul_le_mul_left 4 hi').trans <| by
        simpa [Nat.mul_comm] using (Nat.div_mul_le_self n 4)
    omega
  have hmul :
      (3 * Nat.choose n i) * (i + 1) ≤ Nat.choose n (i + 1) * (i + 1) := by
    calc
      (3 * Nat.choose n i) * (i + 1)
          = Nat.choose n i * (3 * (i + 1)) := by ring
      _ ≤ Nat.choose n i * (n - i) := Nat.mul_le_mul_left _ hineq
      _ = Nat.choose n (i + 1) * (i + 1) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Nat.choose_succ_right_eq n i).symm
  exact Nat.le_of_mul_le_mul_right (by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    ) (Nat.succ_pos i)

/-- A binary Hamming ball of radius `n/4` has size at most `2 * (n choose n/4)`. -/
private lemma hammingBall_card_quarter_le_two_mul_choose
    (n : ℕ) (a : BoolInput n) :
    ((hammingBall (n := n) (α := Bool) a (n / 4)).card : ℝ) ≤
      2 * (Nat.choose n (n / 4) : ℝ) := by
  let r : ℕ := n / 4
  let b : ℕ → ℝ := fun i => Nat.choose n i
  have hstep : ∀ i ∈ Finset.range r, (3 : ℝ) * b i ≤ b (i + 1) := by
    intro i hi
    have hi' : i < n / 4 := by simpa [r] using Finset.mem_range.mp hi
    have hnat : 3 * Nat.choose n i ≤ Nat.choose n (i + 1) :=
      choose_three_mul_le_succ_choose_quarter (n := n) hi'
    have hreal : (3 : ℝ) * (Nat.choose n i : ℝ) ≤ (Nat.choose n (i + 1) : ℝ) := by
      exact_mod_cast hnat
    simpa [b] using hreal
  have hsum2 : (2 : ℝ) * (Finset.sum (Finset.range r) b) ≤ b r := by
    calc
      (2 : ℝ) * (Finset.sum (Finset.range r) b)
          = Finset.sum (Finset.range r) (fun i => b i + b i) := by
              simp [two_mul, Finset.sum_add_distrib]
      _ = Finset.sum (Finset.range r) (fun i => (2 : ℝ) * b i) := by
            simp [two_mul]
      _ ≤ Finset.sum (Finset.range r) (fun i => b (i + 1) - b i) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            linarith [hstep i hi]
      _ = b r - b 0 := by
            calc
              Finset.sum (Finset.range r) (fun i => b (i + 1) - b i)
                  = Finset.sum (Finset.range r) (fun i => b (i + 1)) -
                      Finset.sum (Finset.range r) b := by
                        simp [Finset.sum_sub_distrib]
              _ = b r - b 0 := by
                    have hsub :
                        Finset.sum (Finset.range r) b -
                            Finset.sum (Finset.range r) (fun i => b (i + 1)) = b 0 - b r := by
                      simpa [Finset.sum_sub_distrib] using (Finset.sum_range_sub' b r)
                    linarith
      _ ≤ b r := by
            have hb0 : 0 ≤ b 0 := by positivity
            linarith
  have hsum_full : Finset.sum (Finset.range (r + 1)) b ≤ 2 * b r := by
    rw [Finset.sum_range_succ]
    have hhalf : Finset.sum (Finset.range r) b ≤ b r / 2 := by linarith [hsum2]
    linarith [hhalf]
  have hcard :
      ((hammingBall (n := n) (α := Bool) a r).card : ℝ) =
        Finset.sum (Finset.range (r + 1)) b := by
    have := hammingBall_card (n := n) (α := Bool) a r
    simpa [ballVol_binary, b] using congrArg (fun t : ℕ => (t : ℝ)) this
  have hfinal : ((hammingBall (n := n) (α := Bool) a r).card : ℝ) ≤ 2 * b r := by
    linarith [hcard, hsum_full]
  simpa [r, b] using hfinal

/-- Rational upper bound on `exp 1` used in the final numerical estimate. -/
private lemma exp_one_le_68_div_25 : Real.exp 1 ≤ (68 / 25 : ℝ) := by
  have h :=
    Real.exp_bound' (x := (1 : ℝ)) (by positivity) (by norm_num) (n := 5) (by positivity)
  have h' := h
  have hsum :
      (∑ m ∈ Finset.range 5, (1 : ℝ) ^ m / m.factorial) =
        (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum' : (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24 : ℝ) = (65 / 24 : ℝ) := by norm_num
  have htail : (1 : ℝ) ^ 5 * (5 + 1) / (Nat.factorial 5 * 5 : ℝ) = (1 / 100 : ℝ) := by
    norm_num
  have h'' :
      (∑ m ∈ Finset.range 5, (1 : ℝ) ^ m / m.factorial) +
        (1 : ℝ) ^ 5 * (5 + 1) / (Nat.factorial 5 * 5 : ℝ) ≤ (68 / 25 : ℝ) := by
    rw [hsum, hsum', htail]
    norm_num
  exact h'.trans h''

/-- For large `n`, the ratio `n / ⌊n/4⌋` is bounded by `101/25`. -/
private lemma div_nat_div_four_le_101_25
    (n : ℕ) (hn300 : 300 ≤ n) :
    ((n : ℝ) / ((n / 4 : ℕ) : ℝ)) ≤ (101 / 25 : ℝ) := by
  let k : ℕ := n / 4
  have hk75 : 75 ≤ k := by
    dsimp [k]
    omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (show 0 < (75 : ℕ) by decide) hk75
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hmod_nat : n % 4 ≤ 3 := by
    omega
  have hmod : (((n % 4 : ℕ) : ℝ) ≤ 3) := by exact_mod_cast hmod_nat
  have hdecomp :
      (n : ℝ) = 4 * (k : ℝ) + ((n % 4 : ℕ) : ℝ) := by
    have hnat : n = 4 * k + n % 4 := by
      dsimp [k]
      omega
    have hcast := congrArg (fun t : ℕ => (t : ℝ)) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using hcast
  have hratio :
      (n : ℝ) / (k : ℝ) = 4 + (((n % 4 : ℕ) : ℝ) / (k : ℝ)) := by
    calc
      (n : ℝ) / (k : ℝ) = (4 * (k : ℝ) + ((n % 4 : ℕ) : ℝ)) / (k : ℝ) := by rw [hdecomp]
      _ = 4 + (((n % 4 : ℕ) : ℝ) / (k : ℝ)) := by
            rw [add_div]
            have hmul : (4 * (k : ℝ)) / (k : ℝ) = 4 := by field_simp [hk_ne]
            simp [hmul]
  have hfrac1 : (((n % 4 : ℕ) : ℝ) / (k : ℝ)) ≤ 3 / (k : ℝ) := by
    exact div_le_div_of_nonneg_right hmod hk_pos.le
  have hk75_real : (75 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk75
  have hfrac2 : 3 / (k : ℝ) ≤ (3 / 75 : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hk75_real
  calc
    (n : ℝ) / ((n / 4 : ℕ) : ℝ) = (n : ℝ) / (k : ℝ) := by rfl
    _ = 4 + (((n % 4 : ℕ) : ℝ) / (k : ℝ)) := hratio
    _ ≤ 4 + (3 / 75 : ℝ) := by linarith [hfrac1, hfrac2]
    _ ≤ (101 / 25 : ℝ) := by norm_num

/-- Binomial coefficient bound at quarter radius used in the indexing argument. -/
private lemma choose_quarter_le_eleven_pow
    (n : ℕ) (hn300 : 300 ≤ n) :
    Nat.choose n (n / 4) ≤ 11 ^ (n / 4) := by
  let k : ℕ := n / 4
  have hk_pos_nat : 0 < k := by
    dsimp [k]
    omega
  have hchoose :
      (Nat.choose n k : ℝ) ≤ (n ^ k : ℝ) / (k.factorial : ℝ) := by
    simpa [k] using
      (Nat.choose_le_pow_div (r := k) (n := n) :
        (Nat.choose n k : ℝ) ≤ (n ^ k : ℝ) / (k.factorial : ℝ))
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    have hk_one : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hk_pos_nat
    have hpi_one : (1 : ℝ) ≤ Real.pi := by
      have hpi_three : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have hmul : (1 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by nlinarith
    exact (Real.one_le_sqrt).2 hmul
  have hkpow_nonneg : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
  have hkfac_lower :
      ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k
          = (1 : ℝ) * (((k : ℝ) / Real.exp 1) ^ k) := by ring
      _ ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) * (((k : ℝ) / Real.exp 1) ^ k) := by
            gcongr
      _ ≤ (k.factorial : ℝ) := by
            exact Stirling.le_factorial_stirling k
  have hdiv :
      (n ^ k : ℝ) / (k.factorial : ℝ) ≤
        (n ^ k : ℝ) / (((k : ℝ) / Real.exp 1) ^ k) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkfac_lower
  have hchoose' :
      (Nat.choose n k : ℝ) ≤ (n ^ k : ℝ) / (((k : ℝ) / Real.exp 1) ^ k) :=
    hchoose.trans hdiv
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk_pos_nat
  have hsimp :
      (n ^ k : ℝ) / (((k : ℝ) / Real.exp 1) ^ k) =
        (Real.exp 1 * ((n : ℝ) / (k : ℝ))) ^ k := by
    rw [← div_pow]
    have hdiv :
        (n : ℝ) / ((k : ℝ) / Real.exp 1) = Real.exp 1 * ((n : ℝ) / (k : ℝ)) := by
      field_simp [hk_ne]
    simp [hdiv]
  have hratio :
      ((n : ℝ) / (k : ℝ)) ≤ (101 / 25 : ℝ) := by
    simpa [k] using div_nat_div_four_le_101_25 n hn300
  have hbase :
      Real.exp 1 * ((n : ℝ) / (k : ℝ)) ≤ ((68 / 25 : ℝ) * (101 / 25 : ℝ)) := by
    have hmul := mul_le_mul exp_one_le_68_div_25 hratio (by positivity) (by positivity)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hpow :
      (Real.exp 1 * ((n : ℝ) / (k : ℝ))) ^ k ≤
        (((68 / 25 : ℝ) * (101 / 25 : ℝ)) ^ k) := by
    gcongr
  have hconst :
      ((68 / 25 : ℝ) * (101 / 25 : ℝ)) ≤ (11 : ℝ) := by
    norm_num
  have hconst_pow :
      (((68 / 25 : ℝ) * (101 / 25 : ℝ)) ^ k) ≤ (11 : ℝ) ^ k := by
    gcongr
  have hfinal_real : (Nat.choose n k : ℝ) ≤ (11 : ℝ) ^ k := by
    calc
      (Nat.choose n k : ℝ)
          ≤ (n ^ k : ℝ) / (((k : ℝ) / Real.exp 1) ^ k) := hchoose'
      _ = (Real.exp 1 * ((n : ℝ) / (k : ℝ))) ^ k := hsimp
      _ ≤ (((68 / 25 : ℝ) * (101 / 25 : ℝ)) ^ k) := hpow
      _ ≤ (11 : ℝ) ^ k := hconst_pow
  exact_mod_cast (show (Nat.choose n k : ℝ) ≤ (11 : ℝ) ^ k from hfinal_real)

open Classical in
/-- The number of good inputs is bounded by the number of answer vectors times
an upper bound on the quarter-radius Hamming ball volume. -/
private lemma goodInput_card_le
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    let good : Finset (BoolInput n) :=
      Finset.univ.filter (fun x : BoolInput n => ¬ badInput (n := n) p x)
    good.card ≤
      (answerSet (n := n) p).card * (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4)) := by
  intro good
  have hsubset :
      good ⊆
        (answerSet (n := n) p).biUnion
          (fun a : BoolInput n => hammingBall (n := (n : ℕ)) (α := Bool) a ((n : ℕ) / 4)) := by
    intro x hx
    have hx' : ¬ badInput (n := n) p x := (Finset.mem_filter.mp hx).2
    rcases (not_not.mp hx') with ⟨a, haA, hlt⟩
    have hfloor :
        Nat.floor (((n : ℕ) : ℝ) / 4) = (n : ℕ) / 4 := by
      simpa using (Nat.floor_div_eq_div (K := ℝ) (m := (n : ℕ)) (n := 4))
    have hle_floor :
        hammingDist x a ≤ Nat.floor (((n : ℕ) : ℝ) / 4) := by
      exact Nat.le_floor (le_of_lt hlt)
    have hle : hammingDist x a ≤ (n : ℕ) / 4 := by simpa [hfloor] using hle_floor
    have hle' : hammingDist a x ≤ (n : ℕ) / 4 := by simpa [hammingDist_comm] using hle
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨a, haA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle'⟩⟩
  have hcard_union :
      good.card ≤
        ((answerSet (n := n) p).biUnion
          (fun a : BoolInput n =>
            hammingBall (n := (n : ℕ)) (α := Bool) a ((n : ℕ) / 4))).card := by
    exact Finset.card_le_card hsubset
  have hball :
      ∀ a ∈ answerSet (n := n) p,
        (hammingBall (n := (n : ℕ)) (α := Bool) a ((n : ℕ) / 4)).card ≤
          2 * Nat.choose (n : ℕ) ((n : ℕ) / 4) := by
    intro a ha
    have hreal :=
      hammingBall_card_quarter_le_two_mul_choose (n := (n : ℕ)) a
    exact_mod_cast hreal
  have hcard_mul :
      ((answerSet (n := n) p).biUnion
        (fun a : BoolInput n =>
          hammingBall (n := (n : ℕ)) (α := Bool) a ((n : ℕ) / 4))).card ≤
          (answerSet (n := n) p).card * (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4)) := by
    exact Finset.card_biUnion_le_card_mul
      (answerSet (n := n) p)
      (fun a : BoolInput n => hammingBall (n := (n : ℕ)) (α := Bool) a ((n : ℕ) / 4))
      (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4))
      hball
  exact hcard_union.trans hcard_mul

/-- If the one-way cost is at most `n/10` (with `n ≥ 300`), then at least half
of Alice inputs are bad in the answer-vector/Hamming-ball sense. -/
private lemma badInput_card_ge_half_of_small_cost
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (hn300 : 300 ≤ (n : ℕ))
    (hcost : p.cost ≤ (n : ℕ) / 10) :
    2 ^ (((n : ℕ)) - 1) ≤
      (Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)).card := by
  let bad : Finset (BoolInput n) :=
    Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)
  let good : Finset (BoolInput n) :=
    Finset.univ.filter (fun x : BoolInput n => ¬ badInput (n := n) p x)
  have hgood_le0 :
      good.card ≤
        (answerSet (n := n) p).card * (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4)) := by
    simpa [good] using goodInput_card_le (n := n) p
  have hA_le : (answerSet (n := n) p).card ≤ 2 ^ ((n : ℕ) / 10) := by
    calc
      (answerSet (n := n) p).card ≤ 2 ^ p.cost := answerSet_card_le_pow_cost (n := n) p
      _ ≤ 2 ^ ((n : ℕ) / 10) := Nat.pow_le_pow_right (by decide) hcost
  have hchoose_le :
      Nat.choose (n : ℕ) ((n : ℕ) / 4) ≤ 11 ^ ((n : ℕ) / 4) := by
    exact choose_quarter_le_eleven_pow (n := (n : ℕ)) hn300
  have hgood_le :
      good.card ≤ 2 ^ (((n : ℕ) / 10) + 1) * 11 ^ ((n : ℕ) / 4) := by
    calc
      good.card
          ≤ (answerSet (n := n) p).card * (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4)) := hgood_le0
      _ ≤ (2 ^ ((n : ℕ) / 10)) * (2 * 11 ^ ((n : ℕ) / 4)) := by gcongr
      _ = 2 ^ (((n : ℕ) / 10) + 1) * 11 ^ ((n : ℕ) / 4) := by
            ring_nf
  have h11pow :
      11 ^ (2 * ((n : ℕ) / 4)) ≤ 2 ^ (7 * ((n : ℕ) / 4)) := by
    calc
      11 ^ (2 * ((n : ℕ) / 4)) = (11 ^ 2) ^ ((n : ℕ) / 4) := by rw [Nat.pow_mul]
      _ ≤ (2 ^ 7) ^ ((n : ℕ) / 4) := by
            exact Nat.pow_le_pow_left (by norm_num : 11 ^ 2 ≤ 2 ^ 7) _
      _ = 2 ^ (7 * ((n : ℕ) / 4)) := by rw [Nat.pow_mul]
  have hsq :
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1) * 11 ^ ((n : ℕ) / 4)) ^ 2 := by
    exact Nat.pow_le_pow_left hgood_le 2
  have hsq' :
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * (11 ^ ((n : ℕ) / 4)) ^ 2 := by
    simpa [Nat.mul_pow] using hsq
  have hsq'' :
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 11 ^ (2 * ((n : ℕ) / 4)) := by
    have hpow11 : (11 ^ ((n : ℕ) / 4)) ^ 2 = 11 ^ (2 * ((n : ℕ) / 4)) := by
      rw [← Nat.pow_mul, Nat.mul_comm]
    calc
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * (11 ^ ((n : ℕ) / 4)) ^ 2 := hsq'
      _ = (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 11 ^ (2 * ((n : ℕ) / 4)) := by rw [hpow11]
  have hsq''' :
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 2 ^ (7 * ((n : ℕ) / 4)) := by
    calc
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 11 ^ (2 * ((n : ℕ) / 4)) := hsq''
      _ ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 2 ^ (7 * ((n : ℕ) / 4)) := by gcongr
  have hsq'''' :
      good.card ^ 2 ≤ 2 ^ (2 * (((n : ℕ) / 10) + 1)) * 2 ^ (7 * ((n : ℕ) / 4)) := by
    have hpow2 : (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 = 2 ^ (2 * (((n : ℕ) / 10) + 1)) := by
      rw [← Nat.pow_mul, Nat.mul_comm]
    calc
      good.card ^ 2 ≤ (2 ^ (((n : ℕ) / 10) + 1)) ^ 2 * 2 ^ (7 * ((n : ℕ) / 4)) := hsq'''
      _ = 2 ^ (2 * (((n : ℕ) / 10) + 1)) * 2 ^ (7 * ((n : ℕ) / 4)) := by rw [hpow2]
  have hexp :
      2 * (((n : ℕ) / 10) + 1) + 7 * ((n : ℕ) / 4) ≤ 2 * (((n : ℕ)) - 1) := by
    omega
  have hsq_bound :
      good.card ^ 2 ≤ (2 ^ (((n : ℕ)) - 1)) ^ 2 := by
    calc
      good.card ^ 2
          ≤ 2 ^ (2 * (((n : ℕ) / 10) + 1)) * 2 ^ (7 * ((n : ℕ) / 4)) := hsq''''
      _ = 2 ^ (2 * (((n : ℕ) / 10) + 1) + 7 * ((n : ℕ) / 4)) := by
            rw [← Nat.pow_add]
      _ ≤ 2 ^ (2 * (((n : ℕ)) - 1)) := by
            exact Nat.pow_le_pow_right (by decide) hexp
      _ = (2 ^ (((n : ℕ)) - 1)) ^ 2 := by
            rw [Nat.mul_comm, Nat.pow_mul]
  have hgood_half : good.card ≤ 2 ^ (((n : ℕ)) - 1) := by
    by_contra hgt
    have hgt' : 2 ^ (((n : ℕ)) - 1) < good.card := Nat.lt_of_not_ge hgt
    have hsq_gt : (2 ^ (((n : ℕ)) - 1)) ^ 2 < good.card ^ 2 := by
      exact Nat.pow_lt_pow_left hgt' (by decide : (2 : ℕ) ≠ 0)
    exact (not_lt_of_ge hsq_bound) hsq_gt
  have hsplit :
      bad.card + good.card = 2 ^ (n : ℕ) := by
    have h :
        bad.card + good.card = (Finset.univ : Finset (BoolInput n)).card := by
      simpa [bad, good] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (BoolInput n)))
          (p := fun x : BoolInput n => badInput (n := n) p x))
    have huniv : ((Finset.univ : Finset (BoolInput n)).card) = 2 ^ (n : ℕ) := by
      simp [BoolInput, Fintype.card_pi, Fintype.card_bool, Finset.card_univ, Finset.prod_const]
    simpa [huniv] using h
  have htwo_pow : 2 ^ (n : ℕ) = 2 ^ (((n : ℕ)) - 1) + 2 ^ (((n : ℕ)) - 1) := by
    have hn_pos : 0 < (n : ℕ) := by omega
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos) with ⟨m, hm⟩
    rw [hm, Nat.succ_sub_one, Nat.pow_succ]
    ring
  have hsum :
      2 ^ (((n : ℕ)) - 1) + good.card ≤ bad.card + good.card := by
    calc
      2 ^ (((n : ℕ)) - 1) + good.card
          ≤ 2 ^ (((n : ℕ)) - 1) + 2 ^ (((n : ℕ)) - 1) := by gcongr
      _ = 2 ^ (n : ℕ) := htwo_pow.symm
      _ = bad.card + good.card := hsplit.symm
  exact Nat.le_of_add_le_add_right hsum

/-- Deterministic distributional lower bound for indexing under the uniform input
distribution: any one-way protocol of cost at most `n/10` (for `n ≥ 300`) has
distributional error strictly bigger than `1/9`. -/
theorem one_ninth_lt_distributionalError_of_cost_le
    (hn300 : 300 ≤ (n : ℕ)) :
    ∀ (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool),
      p.cost ≤ (n : ℕ) / 10 →
      p.distributionalError (μ := indexingInputDist n) (indexing n) > (1 / 9 : ℝ) := by
  intro p hcost
  have hbad :
      2 ^ (((n : ℕ)) - 1) ≤
        (Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)).card := by
    exact badInput_card_ge_half_of_small_cost (n := n) p hn300 hcost
  have herr_ge : p.distributionalError (μ := indexingInputDist n) (indexing n) ≥ (1 / 8 : ℝ) :=
    distributionalError_ge_one_eighth_of_bad_half (n := n) p hbad
  linarith

/-- Distributional one-way lower-bound hypothesis for indexing at error `ε`
and cost budget `c`. -/
def deterministicOneWayDistributionalLowerBound (ε : ℝ) (c : ℕ) : Prop :=
  ∀ (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool),
    p.cost ≤ c →
    p.distributionalError (μ := indexingInputDist n) (indexing n) > ε

/-- Packaged form of `one_ninth_lt_distributionalError_of_cost_le`
using the repository's standard distributional-lower-bound predicate. -/
theorem deterministicOneWayDistributionalLowerBound_one_ninth_of_large
    (hn300 : 300 ≤ (n : ℕ)) :
    deterministicOneWayDistributionalLowerBound n (1 / 9 : ℝ) ((n : ℕ) / 10) := by
  intro p hcost
  exact one_ninth_lt_distributionalError_of_cost_le (n := n) hn300 p hcost

/-- Any distributional lower bound against the uniform indexing distribution yields a one-way
public-coin lower bound via minimax. -/
theorem lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound
    {ε : ℝ} {c : ℕ}
    (h : deterministicOneWayDistributionalLowerBound n ε c) :
    c < PublicCoin.OneWay.communicationComplexity (indexing n) ε := by
  exact PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt
    (f := indexing n) (ε := ε) (n := c) (μ := indexingInputDist n) h

/-- Specialization of
`lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound` to the common
constants used in the indexing proof. -/
theorem div_ten_lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound
    (h : deterministicOneWayDistributionalLowerBound n (1 / 8 : ℝ) ((n : ℕ) / 10)) :
    ((((n : ℕ) / 10 : ℕ) : ENat)) <
      PublicCoin.OneWay.communicationComplexity (indexing n) (1 / 8 : ℝ) := by
  exact lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound (n := n) h

/-- Linear public-coin one-way lower bound for indexing at error threshold `1/9`
for all sufficiently large input lengths. -/
theorem div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth
    (hn300 : 300 ≤ (n : ℕ)) :
    ((((n : ℕ) / 10 : ℕ) : ENat)) <
      PublicCoin.OneWay.communicationComplexity (indexing n) (1 / 9 : ℝ) := by
  exact lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound (n := n)
    (deterministicOneWayDistributionalLowerBound_one_ninth_of_large (n := n) hn300)

end Functions.Indexing

end CommunicationComplexity
