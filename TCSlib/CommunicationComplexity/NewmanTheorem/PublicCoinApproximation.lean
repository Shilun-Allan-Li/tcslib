/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public Coin Approximation

The discretisation step of Newman's theorem for public-coin protocols: a public-coin
finite-message protocol whose shared randomness is drawn from an arbitrary finite probability
space `Ω` is replaced by one whose randomness is a coin tape of fair bits, at the cost of an
arbitrarily small additive increase `δ` in the error and no change in communication. The
construction pulls the protocol back along a map `φ : CoinTape n → Ω` whose pushforward of
the uniform measure approximates the given measure on `Ω` to within `δ` on every event
(`Internal.single_coin_approx` from `PrivateCoinApproximation`). This is what allows the
communication-complexity measures of this topic to quantify over coin tapes only.

## Main definitions

- `PublicCoin.FiniteMessage.Protocol.toCoinTape`: converts a public-coin finite-message
  protocol over an arbitrary finite probability space to one using `CoinTape` randomness,
  given a slack `δ > 0`.

## Main results

- `PublicCoin.FiniteMessage.Protocol.toCoinTape_complexity`: the `CoinTape` approximation
  has the same complexity as the original protocol.
- `PublicCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies`: the `CoinTape`
  approximation preserves `ApproxSatisfies` up to the given slack `δ`.

## References

* [New91] I. Newman, "Private vs. common random bits in communication complexity",
  *Information Processing Letters* 39(2):67–71, 1991.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

open MeasureTheory

namespace CommunicationComplexity

namespace PublicCoin

/-- The coin-tape approximation of a public-coin finite-message protocol `p` over an
arbitrary finite probability space `Ω` with slack `δ > 0`: a length `n` together with a
protocol over `CoinTape n` obtained by pulling `p` back along a map `φ : CoinTape n → Ω`
(chosen by `Internal.single_coin_approx`) under which every event of `Ω` is approximated to
within `δ`. The result has the same complexity as `p` and, on every input, an error
probability at most `δ` larger. -/
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (n : ℕ), FiniteMessage.Protocol (CoinTape n) X Y α :=
  let data := Internal.single_coin_approx (Ω := Ω) δ hδ
  let n := data.choose
  let φ := data.choose_spec.choose
  ⟨n, p.comap (Prod.map φ id) (Prod.map φ id)⟩

/-- The coin-tape approximation of a public-coin finite-message protocol `p` has exactly the
complexity of `p`: pulling back along the map on randomness changes no message. -/
@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]

/-- If a public-coin finite-message protocol `p` over a finite probability space
`ε`-satisfies a relation `Q`, then its coin-tape approximation with slack `δ > 0`
`(ε + δ)`-satisfies `Q`: on each input the failure event of the approximation is the
preimage under `φ` of the failure event of `p`, whose measure exceeds that of the original
event by at most `δ`.

**Proof sketch.** Fix an input `(x, y)` and unfold `toCoinTape` to expose the tape length and
the map `φ` supplied by `single_coin_approx`, together with its guarantee that the preimage
under `φ` of any event has measure at most that of the event plus `δ`. (1) The failure event of
the pulled-back protocol on `(x, y)` is the preimage under `φ` of the failure event `S` of `p`
on `(x, y)`, because the pulled-back protocol runs `p` on `φ ω`. (2) Hence its measure is at
most the measure of `S` plus `δ`, and the measure of `S` is at most `ε` since `p`
`ε`-satisfies `Q`. -/
theorem FiniteMessage.Protocol.toCoinTape_approxSatisfies
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (Q : X → Y → α → Prop)
    (ε δ : ℝ) (hδ : 0 < δ)
    (hp : p.ApproxSatisfies Q ε) :
    (p.toCoinTape δ hδ).2.ApproxSatisfies Q (ε + δ) := by
  intro x y
  simp only [FiniteMessage.Protocol.toCoinTape]
  set data := Internal.single_coin_approx (Ω := Ω) δ hδ
  set φ := data.choose_spec.choose
  have happrox := data.choose_spec.choose_spec
  -- The error set under the new protocol is the preimage under φ
  let S := {ω : Ω | ¬Q x y (p.rrun x y ω)}
  have hset : {ω : CoinTape data.choose |
      ¬Q x y (FiniteMessage.Protocol.rrun
        (p.comap (Prod.map φ id) (Prod.map φ id)) x y ω)} =
      φ ⁻¹' S := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, S,
      FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.comap_run, Prod.map,
      Function.id_def]
  rw [hset]
  calc volume.real (φ ⁻¹' S : Set (CoinTape data.choose))
      ≤ volume.real S + δ := happrox S
    _ ≤ ε + δ := by
        have hpS : volume.real S ≤ ε := by simpa [S] using hp x y
        linarith

end PublicCoin

end CommunicationComplexity
