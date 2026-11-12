/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FuncIndexing.Basic
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
# Indexing: the linear public-coin one-way lower bound

The linear public-coin one-way lower bound of Kremer–Nisan–Ron for the Index problem
(`Functions.Indexing.indexing`, defined in `DeterministicCC/FuncIndexing/Basic.lean`) via
Yao's distributional method [Rou16, Thm 2.4], with explicit constants: for `n ≥ 300`, every
protocol with error `1/9` needs more than `n/10` bits.

## Main definitions

- `Functions.Indexing.deterministicOneWayDistributionalLowerBound`: the hypothesis of the
  one-way minimax step, specialised to Index under the uniform distribution.

## Main results

- `Functions.Indexing.distributionalError_ge_one_eighth_of_bad_half`: if at least half of
  Alice's inputs are far from every answer vector, the distributional error is at least `1/8`.
- `Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le`: for `n ≥ 300`, every
  deterministic one-way protocol of cost at most `n/10` errs with probability more than
  `1/9` under the uniform distribution.
- `Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth`: for
  `n ≥ 300`, the public-coin one-way complexity of Index at error `1/9` exceeds `n/10`.

### Counting lemmas

The section `### Counting lemmas for the distributional indexing lower bound` proves the
Claim of [Rou16, Thm 2.4 proof]: for `n ≥ 300` and cost at most `n/10`, at least `2^(n-1)`
inputs are bad. The Claim is stated for `c` sufficiently small and `n` sufficiently large;
the values `c = 1/10`, `n ≥ 300` are the ones Rou16's proof suggests ("say .1",
"say ≥ 300"), here made part of the hypotheses. Rou16 bounds the radius-`n/4` Hamming
ball by `n (4e)^(n/4)`; here the ball is bounded by `2 · C(n, n/4) ≤ 2 · 11^(n/4)` (the
constant `11` replaces `4e` and the factor `2` replaces `n`) with fully explicit numerics
(`e ≤ 68/25`, `n / ⌊n/4⌋ ≤ 101/25`, `11² ≤ 2⁷`).

## References

* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KNR99] I. Kremer, N. Nisan, D. Ron, "On randomized one-round communication complexity",
  *Computational Complexity* 8(1):21–49, 1999.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Functions.Indexing

open Deterministic
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable (n : ℕ+)

open Classical in
/-- The answer vector `a(m)` of a message `m`: the `n`-bit string of Bob's outputs
`decode m i` over all indices `i`, for a fixed received one-way message `m`
[Rou16, Thm 2.4 proof] (the answer vector `a(z)`). -/
private def answerVector
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (m : p.Message) : BoolInput n :=
  fun i => p.decode m i

open Classical in
/-- The finite set `A` of all answer vectors `a(m)` as `m` ranges over the protocol's
messages [Rou16, Thm 2.4 proof] (the set `A` of answer vectors, of size at most `2^{cn}`). -/
private def answerSet
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) : Finset (BoolInput n) :=
  Finset.image (answerVector (n := n) p) Finset.univ

open Classical in
/-- Alice's input `x` is *bad* for the protocol if no realizable answer vector `a ∈ A` is
within Hamming distance strictly less than `n/4` of `x` [Rou16, Thm 2.4 proof] (`x` is
good if some `a ∈ A` has `d_H(x, a) < n/4`, and bad otherwise). The radius is the real
number `n/4`, not its floor. -/
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

/-- For a fixed input string `x`, the number of indices `i` on which the protocol errs equals
the Hamming distance between `x` and the answer vector of the message `send x`
[Rou16, Thm 2.4 proof, eq. (2.1)] (stated there as the probability `d_H(x, a(z)) / n` over
a uniform `i`; here the unnormalised count). -/
private lemma mismatchSubtype_card_eq_hammingDist
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) :
    Fintype.card (mismatchSubtype (n := n) p x) =
      hammingDist x (answerVector (n := n) p (p.send x)) := by
  classical
  unfold hammingDist
  simpa [mismatchSubtype, Deterministic.OneWay.Protocol.run, indexing, answerVector, ne_comm] using
    (Fintype.card_subtype (p := fun i : Fin n => p.decode (p.send x) i ≠ x i))

/-- The number of incorrect input pairs `(x, i)` equals the sum over all strings `x` of the
number of indices `i` on which the protocol errs at `x` (a Fubini count over the sigma type
`badPairEquivSigma`). -/
private lemma badPairSubtype_card_eq_sum
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    Fintype.card (badPairSubtype (n := n) p) =
      ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := by
  calc
    Fintype.card (badPairSubtype (n := n) p) =
        Fintype.card (Σ x : BoolInput n, mismatchSubtype (n := n) p x) := by
          exact Fintype.card_congr (badPairEquivSigma (n := n) p)
    _ = ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := Fintype.card_sigma

/-- A one-way protocol of cost `c` realises at most `2^c` distinct answer vectors: the answer
set is the image of the message type, which has at most `2^c` elements
[Rou16, Thm 2.4 proof] (at most `2^{cn}` answer vectors). -/
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

/-- If `x` is a bad input then its Hamming distance to the answer vector of its own message
`send x` is at least `n/4` (that vector lies in the answer set, and a bad `x` is at distance
at least `n/4` from every member of the answer set). -/
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

/-- If at least `2^(n-1)` of Alice's `2^n` inputs are bad for a deterministic one-way
protocol `p` (no answer vector of `p` within Hamming distance `n/4`), then `p` errs with
probability at least `1/8` on a uniformly random pair `(x, i)`
[Rou16, Thm 2.4 proof, 'The Claim implies the theorem'] (each bad `x` contributes
conditional error at least `1/4`, and half the inputs are bad). The source phrases this as
a conditional-expectation decomposition; here it is a direct count of erroneous pairs.

**Proof sketch.** Write `g x` for the number of indices `i` on which `p` errs at `x`.
Split the sum of `g` over all strings into the bad and the good ones, and drop the
(nonnegative) good part. For each bad `x`, `g x` is the Hamming distance from `x` to the
answer vector of its own message, hence at least `n/4`; so the sum over bad inputs is at
least `|bad| · n/4 ≥ 2^(n-1) · n/4`. The total number of erroneous pairs `(x, i)` is exactly
this sum. Unfolding the distributional error under the uniform measure gives the ratio of
the number of erroneous pairs to `|inputs| = 2^n · n`, so the error is at least
`(2^(n-1) · n/4) / (2^n · n) = 1/8`. -/
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
  -- Step 1: split the sum of mismatch counts into bad and good inputs; drop the good part.
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
  -- Step 2: each bad input contributes at least `n/4` mismatches.
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
  -- Step 3: the number of erroneous pairs is the total mismatch count, at least
  -- `2^(n-1) · n/4`.
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
  -- Step 4: unfold the distributional error under the uniform measure as the ratio
  -- `|erroneous pairs| / |inputs|`, with `|inputs| = 2^n · n`.
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
  -- Step 5: divide the count by `2^n · n` and evaluate `(2^(n-1) · n/4) / (2^n · n) = 1/8`.
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

/-! ### Counting lemmas for the distributional indexing lower bound

This section proves the Claim of [Rou16, Thm 2.4 proof]: for `n ≥ 300` and cost at most
`n/10`, at least `2^(n-1)` inputs are bad. The Claim is stated for `c` sufficiently small
and `n` sufficiently large; the values `c = 1/10`, `n ≥ 300` are the ones Rou16's proof
suggests ("say .1", "say ≥ 300"), here made part of the hypotheses. Rou16 bounds the
radius-`n/4` Hamming ball by `n (4e)^(n/4)`; here the ball is bounded by
`2 · C(n, n/4) ≤ 2 · 11^(n/4)` (the constant `11` replaces `4e` and the factor `2`
replaces `n`) with fully explicit numerics (`e ≤ 68/25`, `n / ⌊n/4⌋ ≤ 101/25`,
`11² ≤ 2⁷`). -/

/-- For indices `i` strictly below `n/4`, the binomial coefficients grow by at least a factor
of `3`.
This is the quantitative step used to control the partial binomial sum up to `n/4`.

**Proof sketch.** Step 1: from `i + 1 ≤ ⌊n/4⌋` get `4(i + 1) ≤ n`, hence
`3(i + 1) ≤ n − i`. Step 2: multiply through by `i + 1`:
`3 C(n, i) (i + 1) = C(n, i) · 3(i + 1) ≤ C(n, i)(n − i) = C(n, i + 1)(i + 1)`, the last
equality being the absorption identity `Nat.choose_succ_right_eq`. Step 3: cancel the
positive factor `i + 1`. -/
private lemma choose_three_mul_le_succ_choose_quarter
    {n i : ℕ} (hi : i < n / 4) :
    3 * Nat.choose n i ≤ Nat.choose n (i + 1) := by
  -- Step 1: `3(i + 1) ≤ n − i` from `i + 1 ≤ ⌊n/4⌋`.
  have hineq : 3 * (i + 1) ≤ n - i := by
    have hi' : i + 1 ≤ n / 4 := Nat.succ_le_of_lt hi
    have hmul : 4 * (i + 1) ≤ n := by
      exact (Nat.mul_le_mul_left 4 hi').trans <| by
        simpa [Nat.mul_comm] using (Nat.div_mul_le_self n 4)
    omega
  -- Step 2: the inequality multiplied through by `i + 1`, via the absorption identity.
  have hmul :
      (3 * Nat.choose n i) * (i + 1) ≤ Nat.choose n (i + 1) * (i + 1) := by
    calc
      (3 * Nat.choose n i) * (i + 1)
          = Nat.choose n i * (3 * (i + 1)) := by ring
      _ ≤ Nat.choose n i * (n - i) := Nat.mul_le_mul_left _ hineq
      _ = Nat.choose n (i + 1) * (i + 1) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Nat.choose_succ_right_eq n i).symm
  -- Step 3: cancel the positive factor `i + 1`.
  exact Nat.le_of_mul_le_mul_right (by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    ) (Nat.succ_pos i)

/-- A Hamming ball of radius `⌊n/4⌋` in `{0,1}^n` has at most `2 · C(n, ⌊n/4⌋)` points
[Rou16, Thm 2.4 proof, Claim] (there the ball volume `Σ_{i ≤ n/4} C(n, i)` is bounded by
`n (4e)^{n/4}`; here the geometric growth of the summands gives the sharper factor `2`
instead of `n`).

**Proof sketch.** Write `r = ⌊n/4⌋` and `b i = C(n, i)`. For `i < r` the ratio
`C(n, i+1) / C(n, i) = (n - i)/(i + 1)` is at least `3`, so `2 b i ≤ b (i+1) - b i`;
summing this telescopes to `2 Σ_{i < r} b i ≤ b r - b 0 ≤ b r`. Hence the full sum
`Σ_{i ≤ r} b i = Σ_{i < r} b i + b r` is at most `2 b r`. Finally the ball's cardinality is
that full sum (`hammingBall_card` with the binary volume formula). -/
private lemma hammingBall_card_quarter_le_two_mul_choose
    (n : ℕ) (a : BoolInput n) :
    ((hammingBall (n := n) (α := Bool) a (n / 4)).card : ℝ) ≤
      2 * (Nat.choose n (n / 4) : ℝ) := by
  let r : ℕ := n / 4
  let b : ℕ → ℝ := fun i => Nat.choose n i
  -- Step 1: below radius `n/4` each binomial coefficient is at least three times the previous.
  have hstep : ∀ i ∈ Finset.range r, (3 : ℝ) * b i ≤ b (i + 1) := by
    intro i hi
    have hi' : i < n / 4 := by simpa [r] using Finset.mem_range.mp hi
    have hnat : 3 * Nat.choose n i ≤ Nat.choose n (i + 1) :=
      choose_three_mul_le_succ_choose_quarter (n := n) hi'
    have hreal : (3 : ℝ) * (Nat.choose n i : ℝ) ≤ (Nat.choose n (i + 1) : ℝ) := by
      exact_mod_cast hnat
    simpa [b] using hreal
  -- Step 2: telescoping gives `2 Σ_{i<r} C(n,i) ≤ C(n,r)`.
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
  -- Step 3: hence the full partial sum `Σ_{i≤r} C(n,i)` is at most `2 C(n,r)`.
  have hsum_full : Finset.sum (Finset.range (r + 1)) b ≤ 2 * b r := by
    rw [Finset.sum_range_succ]
    have hhalf : Finset.sum (Finset.range r) b ≤ b r / 2 := by linarith [hsum2]
    linarith [hhalf]
  -- Step 4: the ball's cardinality is that partial sum (binary ball-volume formula).
  have hcard :
      ((hammingBall (n := n) (α := Bool) a r).card : ℝ) =
        Finset.sum (Finset.range (r + 1)) b := by
    have := hammingBall_card (n := n) (α := Bool) a r
    simpa [ballVol_binary, b] using congrArg (fun t : ℕ => (t : ℝ)) this
  have hfinal : ((hammingBall (n := n) (α := Bool) a r).card : ℝ) ≤ 2 * b r := by
    linarith [hcard, hsum_full]
  simpa [r, b] using hfinal

/-- Euler's number is at most `68/25 = 2.72` (from the degree-`5` Taylor bound
`Real.exp_bound'`: `e ≤ 65/24 + 1/100`); the rational upper bound on `e` used in
`choose_quarter_le_eleven_pow`. -/
private lemma exp_one_le_68_div_25 : Real.exp 1 ≤ (68 / 25 : ℝ) := by
  have h :=
    Real.exp_bound' (x := (1 : ℝ)) (by positivity) (by norm_num) (n := 5) (by positivity)
  have hsum :
      (∑ m ∈ Finset.range 5, (1 : ℝ) ^ m / m.factorial) =
        (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum' : (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24 : ℝ) = (65 / 24 : ℝ) := by norm_num
  have htail : (1 : ℝ) ^ 5 * (5 + 1) / (Nat.factorial 5 * 5 : ℝ) = (1 / 100 : ℝ) := by
    norm_num [Nat.factorial]
  have h'' :
      (∑ m ∈ Finset.range 5, (1 : ℝ) ^ m / m.factorial) +
        (1 : ℝ) ^ 5 * (5 + 1) / (Nat.factorial 5 * 5 : ℝ) ≤ (68 / 25 : ℝ) := by
    rw [hsum, hsum', htail]
    norm_num
  exact h.trans h''

/-- For `n ≥ 300`, the ratio `n / ⌊n/4⌋` (as a real number) is at most `101/25 = 4.04`.

**Proof sketch.** Write `k = ⌊n/4⌋ ≥ 75`. Since `n = 4k + (n mod 4)` with `n mod 4 ≤ 3`,
the ratio equals `4 + (n mod 4)/k ≤ 4 + 3/75 = 101/25`. -/
private lemma div_nat_div_four_le_101_25
    (n : ℕ) (hn300 : 300 ≤ n) :
    ((n : ℝ) / ((n / 4 : ℕ) : ℝ)) ≤ (101 / 25 : ℝ) := by
  let k : ℕ := n / 4
  -- Step 1: `k = ⌊n/4⌋ ≥ 75`, so `k` is positive.
  have hk75 : 75 ≤ k := by
    dsimp [k]
    omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (show 0 < (75 : ℕ) by decide) hk75
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- Step 2: `n = 4k + (n mod 4)` with `n mod 4 ≤ 3`, so `n/k = 4 + (n mod 4)/k`.
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
  -- Step 3: `(n mod 4)/k ≤ 3/75`, and `4 + 3/75 ≤ 101/25`.
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

/-- For `n ≥ 300`, the central-quarter binomial coefficient satisfies
`C(n, ⌊n/4⌋) ≤ 11^⌊n/4⌋` [Rou16, Thm 2.4 proof, Claim] (there `C(n,k) ≤ (en/k)^k` gives
`(4e)^{n/4}`; the explicit base `11 ≥ 68/25 · 101/25 ≥ e · n/⌊n/4⌋` replaces `4e`; the
Claim is stated for `n` sufficiently large, and `n ≥ 300` is the value Rou16's proof
suggests ("say ≥ 300"), here made a hypothesis).

**Proof sketch.** Write `k = ⌊n/4⌋ ≥ 1`. First `C(n, k) ≤ n^k / k!`. By Stirling's lower
bound `k! ≥ √(2πk) (k/e)^k ≥ (k/e)^k`, so `C(n, k) ≤ n^k / (k/e)^k = (e · n/k)^k`. With
`e ≤ 68/25` and `n/k ≤ 101/25` the base is at most `68/25 · 101/25 ≤ 11`, giving
`C(n, k) ≤ 11^k` over the reals, hence over the naturals. -/
private lemma choose_quarter_le_eleven_pow
    (n : ℕ) (hn300 : 300 ≤ n) :
    Nat.choose n (n / 4) ≤ 11 ^ (n / 4) := by
  let k : ℕ := n / 4
  have hk_pos_nat : 0 < k := by
    dsimp [k]
    omega
  -- Step 1: `C(n, k) ≤ n^k / k!`.
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
  -- Step 2: Stirling's lower bound `k! ≥ √(2πk) (k/e)^k ≥ (k/e)^k`.
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
  -- Step 3: hence `C(n, k) ≤ n^k / (k/e)^k = (e · n/k)^k`.
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
  -- Step 4: numerics: `e · n/k ≤ 68/25 · 101/25 ≤ 11`, so `(e · n/k)^k ≤ 11^k`.
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
  -- Step 5: chain the bounds over `ℝ` and cast back to `ℕ`.
  have hfinal_real : (Nat.choose n k : ℝ) ≤ (11 : ℝ) ^ k := by
    calc
      (Nat.choose n k : ℝ)
          ≤ (n ^ k : ℝ) / (((k : ℝ) / Real.exp 1) ^ k) := hchoose'
      _ = (Real.exp 1 * ((n : ℝ) / (k : ℝ))) ^ k := hsimp
      _ ≤ (((68 / 25 : ℝ) * (101 / 25 : ℝ)) ^ k) := hpow
      _ ≤ (11 : ℝ) ^ k := hconst_pow
  exact_mod_cast (show (Nat.choose n k : ℝ) ≤ (11 : ℝ) ^ k from hfinal_real)

open Classical in
/-- The number of good inputs (those within Hamming distance `< n/4` of some answer vector)
is at most the number of answer vectors times `2 · C(n, ⌊n/4⌋)`
[Rou16, Thm 2.4 proof, Claim] (the good inputs are covered by the `|A|` Hamming balls of
radius `n/4` centred at the answer vectors; the per-ball bound is
`hammingBall_card_quarter_le_two_mul_choose` instead of `n (4e)^{n/4}`).

**Proof sketch.** A good `x` has some answer vector `a` with `d_H(x, a) < n/4`, hence
`d_H(a, x) ≤ ⌊n/4⌋`, so `x` lies in the Hamming ball of radius `⌊n/4⌋` around `a`. Thus the
good inputs are contained in the union of these balls over the answer set. A union of
`|A|` finite sets each of size at most `2 · C(n, ⌊n/4⌋)` has size at most
`|A| · 2 · C(n, ⌊n/4⌋)`. -/
private lemma goodInput_card_le
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    let good : Finset (BoolInput n) :=
      Finset.univ.filter (fun x : BoolInput n => ¬ badInput (n := n) p x)
    good.card ≤
      (answerSet (n := n) p).card * (2 * Nat.choose (n : ℕ) ((n : ℕ) / 4)) := by
  intro good
  -- Step 1: every good input lies in the radius-`⌊n/4⌋` ball around some answer vector.
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
  -- Step 2: bound the union of the balls by `|A|` times the per-ball bound.
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

/-- The Claim of Rou16: if `n ≥ 300` and the one-way protocol `p` has cost at most `n/10`,
then at least `2^(n-1)` of the `2^n` inputs `x` are bad (no answer vector of `p` within
Hamming distance `n/4`) [Rou16, Thm 2.4 proof, Claim] (the Claim is stated for `c`
sufficiently small and `n` sufficiently large; the values `c = 1/10`, `n ≥ 300` are the
ones Rou16's proof suggests ("say .1", "say ≥ 300"), here made part of the hypotheses
and verified by the numerics `|good| ≤ 2^(n/10 + 1) · 11^(n/4)` and `11² ≤ 2⁷`; the
constant `11` replaces Rou16's `4e` and the factor `2` replaces `n` in the ball bound).

**Proof sketch.** By `goodInput_card_le`, `answerSet_card_le_pow_cost` and
`choose_quarter_le_eleven_pow`, the number of good inputs is at most
`2^(⌊n/10⌋ + 1) · 11^⌊n/4⌋`. Square this bound and use `11² ≤ 2⁷` to get
`|good|² ≤ 2^(2(⌊n/10⌋ + 1) + 7⌊n/4⌋)`; for `n ≥ 300` the exponent is at most `2(n - 1)`
(integer arithmetic), so `|good|² ≤ (2^(n-1))²` and hence `|good| ≤ 2^(n-1)`. Since
`|bad| + |good| = 2^n = 2^(n-1) + 2^(n-1)`, this gives `|bad| ≥ 2^(n-1)`. -/
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
  -- Step 1: `|good| ≤ |A| · 2 C(n, n/4) ≤ 2^(n/10 + 1) · 11^(n/4)`.
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
  -- Step 2: square the bound and replace `11^2` by `2^7`, so that
  -- `|good|^2 ≤ 2^(2(n/10 + 1) + 7(n/4))`.
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
  -- Step 3: for `n ≥ 300` the exponent is at most `2(n - 1)`, so `|good|^2 ≤ (2^(n-1))^2`
  -- and therefore `|good| ≤ 2^(n-1)`.
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
  -- Step 4: `|bad| + |good| = 2^n = 2^(n-1) + 2^(n-1)`, hence `|bad| ≥ 2^(n-1)`.
  have hsplit :
      bad.card + good.card = 2 ^ (n : ℕ) := by
    have h :
        bad.card + good.card = (Finset.univ : Finset (BoolInput n)).card := by
      simpa [bad, good] using
        (Finset.filter_card_add_filter_neg_card_eq_card
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

/-- For `n ≥ 300`, every deterministic one-way protocol for Index of cost at most `n/10`
errs with probability strictly greater than `1/9` on a uniformly random pair `(x, i)`
[Rou16, Thm 2.4 proof] (every deterministic one-way protocol with at most `cn` bits errs
with probability at least `1/8` under `D`). Deviations: `c = 1/10` and `n ≥ 300` (the
values Rou16's proof suggests, "say .1", "say ≥ 300") are part of the hypotheses, and
the conclusion is weakened from `≥ 1/8` to the strict `> 1/9`
because the one-way minimax step (`deterministicOneWayDistributionalLowerBound`, used via
`PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt`) needs a
strict inequality. -/
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

/-- The proposition that every deterministic one-way protocol for Index of cost at most `c`
has distributional error strictly greater than `ε` under the uniform input distribution
`indexingInputDist` — the hypothesis of the easy direction of Yao's minimax principle for
one-way protocols [Rou16, Lemma 2.3] (Yao, one-way) as applied in [Rou16, Thm 2.4]. This
predicate is local to this file and specialised to Index and the uniform distribution. -/
def deterministicOneWayDistributionalLowerBound (ε : ℝ) (c : ℕ) : Prop :=
  ∀ (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool),
    p.cost ≤ c →
    p.distributionalError (μ := indexingInputDist n) (indexing n) > ε

/-- For `n ≥ 300`, Index satisfies the distributional one-way lower-bound hypothesis at
error `1/9` and cost budget `n/10`: every deterministic one-way protocol of cost at most
`n/10` has uniform-distributional error greater than `1/9` [Rou16, Lemma 2.3] (Yao, one-way)
applied to [Rou16, Thm 2.4]. This is `one_ninth_lt_distributionalError_of_cost_le` restated
as the predicate `deterministicOneWayDistributionalLowerBound`. -/
theorem deterministicOneWayDistributionalLowerBound_one_ninth_of_large
    (hn300 : 300 ≤ (n : ℕ)) :
    deterministicOneWayDistributionalLowerBound n (1 / 9 : ℝ) ((n : ℕ) / 10) := by
  intro p hcost
  exact one_ninth_lt_distributionalError_of_cost_le (n := n) hn300 p hcost

/-- If every deterministic one-way protocol for Index of cost at most `c` has
uniform-distributional error greater than `ε`, then the public-coin one-way communication
complexity of Index at error `ε` is strictly greater than `c` [Rou16, Lemma 2.3] (Yao's
minimax principle for one-way protocols, easy direction) as used in [Rou16, Thm 2.4]. -/
theorem lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound
    {ε : ℝ} {c : ℕ}
    (h : deterministicOneWayDistributionalLowerBound n ε c) :
    c < PublicCoin.OneWay.communicationComplexity (indexing n) ε := by
  exact PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt
    (f := indexing n) (ε := ε) (n := c) (μ := indexingInputDist n) h

/-- If every deterministic one-way protocol for Index of cost at most `n/10` has
uniform-distributional error greater than `1/8`, then the public-coin one-way communication
complexity of Index at error `1/8` is strictly greater than `n/10` [Rou16, Lemma 2.3] (Yao,
one-way) applied to [Rou16, Thm 2.4] (the constants `1/8` and `cn` of the source). This is
`lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound` at the source's
constants; the headline `div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth`
uses error `1/9` instead, so this lemma has no caller in this file. -/
theorem div_ten_lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound
    (h : deterministicOneWayDistributionalLowerBound n (1 / 8 : ℝ) ((n : ℕ) / 10)) :
    ((((n : ℕ) / 10 : ℕ) : ENat)) <
      PublicCoin.OneWay.communicationComplexity (indexing n) (1 / 8 : ℝ) := by
  exact lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound (n := n) h

/-- For `n ≥ 300`, the public-coin one-way communication complexity of Index on `n` bits at
error `1/9` is strictly greater than `n/10`: a linear lower bound [Rou16, Thm 2.4]
(historically Kremer–Nisan–Ron 1999, [KNR99]). Deviation: the source states
`R→_ε(IND_n) = Ω(n)` for every constant error; here the error is fixed at `1/9`, and the
constant `1/10` and threshold `n ≥ 300` (the values Rou16's proof suggests, "say .1",
"say ≥ 300") are part of the statement. -/
theorem div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth
    (hn300 : 300 ≤ (n : ℕ)) :
    ((((n : ℕ) / 10 : ℕ) : ENat)) <
      PublicCoin.OneWay.communicationComplexity (indexing n) (1 / 9 : ℝ) := by
  exact lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound (n := n)
    (deterministicOneWayDistributionalLowerBound_one_ninth_of_large (n := n) hn300)

end Functions.Indexing

end CommunicationComplexity
