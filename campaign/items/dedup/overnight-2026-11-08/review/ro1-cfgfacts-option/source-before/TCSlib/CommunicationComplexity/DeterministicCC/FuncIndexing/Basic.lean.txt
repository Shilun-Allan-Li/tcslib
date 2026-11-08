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
# Indexing: definition, trivial protocols and exact one-way complexity

The Index problem: Alice holds an `n`-bit string `x`, Bob holds an index `i`, and Bob must
output the bit `x i` [Rou16, §2.4 Definition (Index)]. This file defines the function, the
trivial protocols, proves the exact deterministic one-way complexity `n` (a pigeonhole
argument on Alice's messages) and the `⌈log₂ n⌉ + 1` two-way upper bound, and sets up the
uniform input distribution used by the distributional lower bound in
`DeterministicCC/FuncIndexing/LowerBound.lean`.

## Main definitions

- `Functions.Indexing.indexing`: the Index function `(x, i) ↦ x i`.
- `Functions.Indexing.trivialProtocol`: the one-way protocol in which Alice sends all of `x`.
- `Functions.Indexing.indexingInputDist`: the uniform distribution on pairs `(x, i)`, with
  `x` and `i` independent.

## Main results

- `Functions.Indexing.le_oneWayCommunicationComplexity`: every correct deterministic one-way
  protocol for Index sends at least `n` bits (pigeonhole on Alice's messages).
- `Functions.Indexing.oneWayCommunicationComplexity_eq`: the deterministic one-way
  complexity of Index is exactly `n`.
- `Functions.Indexing.communicationComplexity_le`: the two-way deterministic complexity of
  Index is at most `⌈log₂ n⌉ + 1`.

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

/-- The Index function on `n` bits: Alice holds a string `x : Fin n → Bool`, Bob holds an
index `i : Fin n`, and the answer is Alice's `i`-th bit `x i` [Rou16, §2.4 Definition
(Index)]. -/
def indexing (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i

/-- The trivial one-way protocol for Index: Alice sends her whole string `x` as the message
(`n` bits) and Bob reads off the `i`-th bit [Rou16, §1.7] (the one-way complexity is always
at most Alice's input length). -/
def trivialProtocol : OneWay.Protocol (Fin n → Bool) (Fin n) Bool where
  Message := Fin n → Bool
  send := id
  decode := fun x i => x i

/-- The deterministic one-way communication complexity of Index on `n` bits is at most `n`:
Alice can send all `n` bits of her string [Rou16, §1.7] (witnessed by `trivialProtocol`). -/
theorem oneWayCommunicationComplexity_le :
    OneWay.communicationComplexity (indexing n) ≤ (n : ℕ) := by
  rw [OneWay.communicationComplexity_le_iff]
  refine ⟨trivialProtocol n, (by ext x i; rfl), ?_⟩
  · simp [trivialProtocol, OneWay.Protocol.cost,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow]

/-- The (two-way) deterministic communication complexity of Index on `n` bits is at most
`⌈log₂ n⌉ + 1`: Bob sends his index `i` in `⌈log₂ n⌉` bits and Alice answers with the single
bit `x i` [Rou16, §2.4] (Index is easy for general protocols). The bound is obtained from
the generic `communicationComplexity_le_clog_card_Y_alpha` (Bob's input plus one answer bit),
so it is stated with `Nat.clog 2 n` rather than `≈ log₂ n`. -/
theorem communicationComplexity_le :
    Deterministic.communicationComplexity (indexing n) ≤ Nat.clog 2 (n : ℕ) + 1 := by
  have hbool : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl
  calc
    Deterministic.communicationComplexity (indexing n)
      ≤ Nat.clog 2 (Nat.card (Fin n)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_Y_alpha (indexing n)
    _ = Nat.clog 2 (n : ℕ) + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
        rw [hbool]
        norm_cast

/-- Every correct deterministic one-way protocol for Index on `n` bits has cost at least `n`;
that is, `n ≤ D→(IND_n)` [Rou16, Prop 1.8] (pigeonhole on Alice's messages; Rou16 states it
for Disjointness, and the proof for Index is identical). Together with
`oneWayCommunicationComplexity_le` this gives the exact value `n`, whereas Rou16 only states
the lower bound.

**Proof sketch.** Fix a correct one-way protocol `p`. Alice's message map `send` is
injective: if `send x = send y` then Bob's decoded answers agree on every index `i`, and by
correctness these are `x i` and `y i`, so `x = y`. Hence the number of messages is at least
the number of strings, `2^n`. On the other hand a protocol of cost `c` has at most `2^c`
messages. So `2^n ≤ 2^c`, which forces `n ≤ c`. -/
theorem le_oneWayCommunicationComplexity : n ≤ OneWay.communicationComplexity (indexing n) := by
  rw [OneWay.le_communicationComplexity_iff]
  intro p hp_comp
  -- Step 1: Alice's message map is injective, by correctness of Bob's decoding.
  have hinj : Function.Injective p.send := by
    intro x y heq
    ext i
    have hx := congrFun (congrFun hp_comp x) i
    have hy := congrFun (congrFun hp_comp y) i
    have hm : p.decode (p.send x) i = p.decode (p.send y) i := by
      simpa using congrArg (fun m => p.decode m i) heq
    simpa [OneWay.Protocol.Computes, OneWay.Protocol.run, indexing] using
      hx.symm.trans (hm.trans hy)
  -- Step 2: hence there are at least `2^n` messages.
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card p.Message := by
    exact Fintype.card_le_of_injective p.send hinj
  have hpow_dom : 2 ^ (n : ℕ) ≤ Fintype.card p.Message := by
    simpa [Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] using hcard
  -- Step 3: a protocol of cost `c` has at most `2^c` messages.
  have hcost : Fintype.card p.Message ≤ 2 ^ p.cost := by
    apply Nat.le_pow_clog; linarith
  -- Step 4: `2^n ≤ 2^c` forces `n ≤ c`.
  by_contra!
  have h_bad : 2 ^ p.cost < 2 ^ (n : ℕ) := by
    refine Nat.pow_lt_pow_of_lt (by linarith) this
  omega

/-- The deterministic one-way communication complexity of Index on `n` bits is exactly `n`
[Rou16, Prop 1.8] (pigeonhole on Alice's messages; Rou16 states it for Disjointness, the
Index proof is identical). Rou16 states only the lower bound `≥ n`; the exact value follows
by combining it with the trivial protocol (`oneWayCommunicationComplexity_le`). -/
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
  exact ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

/-- Finite probability-space packaging for uniform `Fin n`. -/
noncomputable instance indexFiniteProbabilitySpace :
    FiniteProbabilitySpace (Fin n) :=
  FiniteProbabilitySpace.of (Fin n)

/-- Finite probability-space packaging for uniform `BoolInput n`. -/
noncomputable instance boolInputFiniteProbabilitySpace :
    FiniteProbabilitySpace (BoolInput n) := by
  change FiniteProbabilitySpace (CoinTape n)
  infer_instance

/-- The hard input distribution for Index: the uniform distribution on pairs `(x, i)`, so
that Alice's string `x` and Bob's index `i` are chosen independently and uniformly
[Rou16, Thm 2.4 proof] (the distribution `D` of the distributional method). Packaged as a
`FiniteProbabilitySpace` structure on `BoolInput n × Fin n` whose measure is
`uniformOn Set.univ`. -/
noncomputable def indexingInputDist :
    FiniteProbabilitySpace (BoolInput n × Fin n) := by
  letI : MeasureSpace (BoolInput n × Fin n) :=
    ⟨ProbabilityTheory.uniformOn Set.univ⟩
  letI : IsProbabilityMeasure (volume : Measure (BoolInput n × Fin n)) := by
    change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
    exact ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
  exact FiniteProbabilitySpace.of (BoolInput n × Fin n)

end Functions.Indexing

end CommunicationComplexity
