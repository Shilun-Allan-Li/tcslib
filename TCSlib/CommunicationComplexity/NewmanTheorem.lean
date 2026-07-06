/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.Derandomization
import TCSlib.CommunicationComplexity.NewmanTheorem.Comparison
import TCSlib.CommunicationComplexity.NewmanTheorem.Minimax
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinOneWay
import TCSlib.CommunicationComplexity.NewmanTheorem.OneWayMinimax
import TCSlib.CommunicationComplexity.NewmanTheorem.Discrepancy
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComposition
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComposition
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncInnerProduct
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncHash
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy
import TCSlib.CommunicationComplexity.NewmanTheorem.KLDivergence
import TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance
import TCSlib.CommunicationComplexity.NewmanTheorem.Pinsker
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Newman's Theorem: Public Coin to Private Coin Reduction

## Main results

- `PublicCoin.newman`: every public-coin protocol can be simulated by a private-coin protocol with only O(log(|X|*|Y|)/epsilon^2) additional random bits
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes`: the Newman private-coin protocol approximately computes the same function as the original public-coin protocol
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity`: the complexity of the Newman protocol equals the log of the number of derandomization samples plus the original protocol's complexity

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity

/-- Unit with the Dirac probability measure. -/
noncomputable instance Unit.measureSpace : MeasureSpace Unit :=
  ⟨Measure.dirac ()⟩

instance Unit.isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure Unit) := by
  constructor
  simp [volume, Unit.measureSpace, Measure.dirac_apply_of_mem (Set.mem_univ ())]

noncomputable instance Unit.finiteProbabilitySpace :
    FiniteProbabilitySpace Unit :=
  FiniteProbabilitySpace.of Unit

namespace PublicCoin

/-- The number of random seeds Alice samples from in the Newman
reduction: `Fin (derandomizationSamples X Y ε c)`. -/
noncomputable abbrev newmanIndexSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :=
  Fin (FiniteMessage.Protocol.derandomizationSamples X Y ε c)

noncomputable instance newmanIndexSpace.fintype
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Fintype (newmanIndexSpace X Y ε c) := inferInstance

noncomputable instance newmanIndexSpace.nonempty
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Nonempty (newmanIndexSpace X Y ε c) :=
  ⟨⟨0, by simp [FiniteMessage.Protocol.derandomizationSamples]⟩⟩

noncomputable instance newmanIndexSpace.measureSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    MeasureSpace (newmanIndexSpace X Y ε c) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance newmanIndexSpace.isProbabilityMeasure
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    IsProbabilityMeasure (volume : Measure (newmanIndexSpace X Y ε c)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

noncomputable instance newmanIndexSpace.finiteProbabilitySpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    FiniteProbabilitySpace (newmanIndexSpace X Y ε c) :=
  FiniteProbabilitySpace.of (newmanIndexSpace X Y ε c)

/-- The Newman reduction: given a public-coin protocol that ε-computes f,
construct a private-coin protocol where Alice samples a random index i
from `newmanIndexSpace` and sends it to Bob. Both then simulate the
public-coin protocol with the i-th seed from a fixed table of good
randomness values (chosen via Chernoff + union bound). -/
noncomputable def FiniteMessage.Protocol.newmanProtocol
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    PrivateCoin.FiniteMessage.Protocol
      (newmanIndexSpace X Y ε c) Unit X Y α :=
  -- Choose good randomness values via Chernoff + union bound
  let ωs := (FiniteMessage.Protocol.exists_good_randomness
    p f ε c hc hp).choose
  -- Alice sends her random index i ∈ newmanIndexSpace to Bob,
  -- then both simulate with ωs(i)
  PrivateCoin.FiniteMessage.Protocol.alice
    (fun _ ω_x => ω_x)
    (fun i => (p.toDeterministic (ωs i)).toPrivateCoin)

theorem FiniteMessage.Protocol.newmanProtocol_ApproxComputes
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hc hp).ApproxComputes f (c * ε) := by
  -- ApproxComputes means: for all x y, P[rrun ≠ f x y] ≤ c * ε
  -- on the product space newmanIndexSpace × Unit
  intro x y
  -- Unfold the protocol definition to get at the run behavior
  unfold newmanProtocol PrivateCoin.FiniteMessage.Protocol.alice
  simp only [PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.run,
    Deterministic.FiniteMessage.Protocol.comap_run]
  set ωs := (exists_good_randomness p f ε c hc hp).choose
  have hωs := (exists_good_randomness p f ε c hc hp).choose_spec
  -- The error set only depends on ω.1 (the index)
  have hset : {ω : newmanIndexSpace X Y ε c × Unit |
      p.run (ωs ω.1, x) (ωs ω.1, y) ≠ f x y} =
      {i | p.run (ωs i, x) (ωs i, y) ≠ f x y} ×ˢ Set.univ := by
    ext ⟨i, u⟩; simp
  rw [hset]
  -- Identify the product-space error probability with the measure of the bad index set.
  rw [FiniteProbabilitySpace.measureReal_prod]
  rw [measureReal_univ_eq_one, mul_one]
  let BadIdx : Set (newmanIndexSpace X Y ε c) :=
    {i | p.run (ωs i, x) (ωs i, y) ≠ f x y}
  -- Now compute that measure in the uniform index space by cardinality.
  rw [Measure.real]
  change (((ProbabilityTheory.uniformOn Set.univ : Measure (newmanIndexSpace X Y ε c))
    BadIdx).toReal ≤ c * ε)
  rw [uniformOn_univ_measureReal_eq_card_filter
    (Ω := newmanIndexSpace X Y ε c) BadIdx]
  simp only [ne_eq, Set.mem_setOf_eq, Fintype.card_fin, BadIdx]
  convert hωs x y using 1
  congr 1
  simp [ωs]
  congr

theorem FiniteMessage.Protocol.newmanProtocol_complexity
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hc hp).complexity =
      Nat.clog 2 (FiniteMessage.Protocol.derandomizationSamples
        X Y ε c) + p.complexity := by
  unfold newmanProtocol PrivateCoin.FiniteMessage.Protocol.alice
  simp only [Deterministic.FiniteMessage.Protocol.complexity,
    Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity,
    PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity]
  -- sup of constant function = constant (since newmanIndexSpace is nonempty)
  rw [Finset.sup_const
    (α := ℕ) (Finset.univ_nonempty (α := newmanIndexSpace X Y ε c)),
    show Fintype.card (newmanIndexSpace X Y ε c) =
      FiniteMessage.Protocol.derandomizationSamples X Y ε c
      from Fintype.card_fin _]

/-- Newman's theorem: for any ε' > c·ε, private-coin communication
complexity at error ε' is at most public-coin complexity at error ε
plus O(log(|X|·|Y|)/ε²) bits. -/
theorem newman
    {X Y α : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → α) (ε ε' : ℝ) (c : ℝ)
    (hc : 1 < c)
    (hε' : c * ε < ε') :
    PrivateCoin.communicationComplexity f ε' ≤
      PublicCoin.communicationComplexity f ε +
        Nat.clog 2
          (FiniteMessage.Protocol.derandomizationSamples
            X Y ε c) := by
  -- Match on the public-coin complexity
  match h : PublicCoin.communicationComplexity f ε with
  | ⊤ => simp
  | (n : ℕ) =>
    -- There exists a public-coin protocol with complexity ≤ n
    obtain ⟨m, p, hp, hc_le⟩ :=
      (PublicCoin.communicationComplexity_le_iff f ε n).mp (le_of_eq h)
    -- Lift to FiniteMessage
    let pfm := PublicCoin.FiniteMessage.Protocol.ofProtocol p
    have hpfm_approx : pfm.ApproxComputes f ε := by
      intro x y
      simp only [pfm, PublicCoin.FiniteMessage.Protocol.rrun,
        Deterministic.FiniteMessage.Protocol.ofProtocol_run]
      exact hp x y
    -- Apply newmanProtocol: get a private-coin FM protocol that (c*ε)-computes f
    let q := pfm.newmanProtocol f ε c hc hpfm_approx
    have hq_approx :=
      FiniteMessage.Protocol.newmanProtocol_ApproxComputes
        pfm f ε c hc hpfm_approx
    -- q (c*ε)-computes f with c*ε < ε', so we can use
    -- communicationComplexity_le_of_finiteMessage
    have hbound :=
      PrivateCoin.communicationComplexity_le_of_finiteMessage
        f ε' (c * ε) hε' q hq_approx
    -- Bound q.complexity
    have hpfm_comp : pfm.complexity = p.complexity :=
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p
    have hq_comp : q.complexity =
        Nat.clog 2 (FiniteMessage.Protocol.derandomizationSamples X Y ε c) +
          pfm.complexity :=
      FiniteMessage.Protocol.newmanProtocol_complexity pfm f ε c hc hpfm_approx
    set t_log := Nat.clog 2
      (FiniteMessage.Protocol.derandomizationSamples X Y ε c)
    -- Goal is: CC ≤ ↑n + ↑t_log
    calc PrivateCoin.communicationComplexity f ε'
        ≤ (q.complexity : ENat) := hbound
      _ = ↑(t_log + pfm.complexity) := by exact_mod_cast hq_comp
      _ = ↑(t_log + p.complexity) := by rw [hpfm_comp]
      _ ≤ ↑(t_log + n) := by exact_mod_cast Nat.add_le_add_left hc_le _
      _ = ↑n + ↑t_log := by push_cast; ring

end PublicCoin

end CommunicationComplexity
