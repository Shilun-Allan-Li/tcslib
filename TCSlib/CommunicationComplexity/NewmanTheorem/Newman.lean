/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.Derandomization
import TCSlib.CommunicationComplexity.NewmanTheorem.Comparison
import PFR.Mathlib.Probability.UniformOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Newman's Theorem: Public Coin to Private Coin Reduction

## Main definitions

- `PublicCoin.newmanIndexSpace`: the index space `Fin (derandomizationSamples X Y ε c)`
  from which Alice samples in the Newman reduction
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol`: the Newman private-coin protocol
  built from a public-coin protocol

## Main results

- `PublicCoin.newman`: every public-coin protocol can be simulated by a private-coin
  protocol with only `⌈log₂ t⌉ = O(log log(|X|·|Y|) + log(1/ε))` additional bits of
  communication, `t = O(log(|X|·|Y|)/ε²)`
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes`: the Newman
  private-coin protocol approximately computes the same function as the original
  public-coin protocol
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity`: the complexity of the
  Newman protocol equals the log of the number of derandomization samples plus the
  original protocol's complexity

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016;
  arXiv:1509.06257.
* [New91] I. Newman, "Private vs. common random bits in communication complexity",
  *Information Processing Letters* 39(2):67–71, 1991.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
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

/-- The index space of the Newman reduction: the finite type
`Fin (derandomizationSamples X Y ε c)` of indices into the table of `t` good seeds, from
which Alice samples uniformly and whose element she sends to Bob.
[RY20, Thm 3.5 proof] (Alice sends the index of one of the `t` good strings). -/
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

/-- The Newman private-coin protocol built from a public-coin protocol `p` that
ε-computes `f`: Alice samples a random index `i` from `newmanIndexSpace` (her private
randomness; Bob has none) and sends it to Bob, and both then run the deterministic
protocol obtained from `p` by fixing its public randomness to the `i`-th seed of a
fixed table of good seeds (the table is the witness of `exists_good_randomness`,
obtained by a Chernoff + union bound). [RY20, Thm 3.5 proof] (Alice sends the index of
one of the `t` good strings). -/
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

/-- The Newman protocol built from a public-coin protocol `p` that ε-computes `f`
computes `f` with error at most `c · ε` on every input: for all `x`, `y`, the probability
over Alice's random index that the protocol's output differs from `f x y` is at most
`c · ε`. [RY20, Thm 3.5 proof].

**Proof sketch.** Fix an input `(x, y)` and let `ωs` be the table of good seeds. After
unfolding, the protocol's output on private randomness `(i, ())` is the output of `p` on
seed `ωs i`. Step 1: the error event on the product space `newmanIndexSpace × Unit` is
the product of the set of bad indices (those `i` for which `p` errs on seed `ωs i`) with
the whole of `Unit`. Step 2: by the product formula for the measure and since `Unit` has
total mass one, the error probability equals the uniform measure of the bad-index set.
Step 3: the uniform measure of a set of indices is its cardinality divided by `t`, which
is at most `c · ε` by the defining property of the good table. -/
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
  -- Step 1: the error set only depends on ω.1 (the index)
  have hset : {ω : newmanIndexSpace X Y ε c × Unit |
      p.run (ωs ω.1, x) (ωs ω.1, y) ≠ f x y} =
      {i | p.run (ωs i, x) (ωs i, y) ≠ f x y} ×ˢ Set.univ := by
    ext ⟨i, u⟩; simp
  rw [hset]
  -- Step 2: identify the product-space error probability with the measure of the bad
  -- index set.
  rw [FiniteProbabilitySpace.measureReal_prod]
  rw [measureReal_univ_eq_one, mul_one]
  let BadIdx : Set (newmanIndexSpace X Y ε c) :=
    {i | p.run (ωs i, x) (ωs i, y) ≠ f x y}
  -- Step 3: compute that measure in the uniform index space by cardinality and apply
  -- the good-table bound.
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

/-- The communication complexity of the Newman protocol is
`⌈log₂ (derandomizationSamples X Y ε c)⌉ + complexity of p`: Alice's index costs
`⌈log₂ t⌉` bits, after which the simulated deterministic protocol costs exactly what `p`
costs. [RY20, Thm 3.5 proof]. The proof unfolds the protocol and evaluates the supremum
over indices of a constant function. -/
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

/-- Newman's theorem: for every `c > 1` and every `ε' > c · ε`, the private-coin
communication complexity of `f` at error `ε'` is at most the public-coin communication
complexity of `f` at error `ε` plus `⌈log₂ (derandomizationSamples X Y ε c)⌉`, i.e. plus
`O(log log(|X|·|Y|) + log(1/((c−1) ε)))` bits (the logarithm of
`t = O(log(|X|·|Y|)/((c−1)² ε²))` seeds). [RY20, Thm 3.5] / [Rou16, Thm 4.9]; historically
[New91]. Deviation: the bound is stated as
`R^priv_{ε'}(f) ≤ R^pub_ε(f) + ⌈log₂ derandomizationSamples⌉` for any `ε' > c · ε` with
`c > 1`, over arbitrary finite input types `X`, `Y`, in place of the textbook
`c + log(n/ε²) + O(1)` at error `2ε`; the slack factor `c > 1` is the Chernoff/union-bound
slack of the derandomization (`exists_good_randomness`; the textbook fixes `c = 2`, hence its
error `2ε`), and the strict inequality `c · ε < ε'` is what the discretisation of private
randomness (`PrivateCoin.communicationComplexity_le_of_finiteMessage`) needs.

**Proof sketch.** Step 1: if the public-coin complexity is infinite there is nothing to
prove; otherwise it equals some `n`, and there is a public-coin protocol `p` that
ε-computes `f` with complexity at most `n`. Step 2: lift `p` to a finite-message
public-coin protocol `pfm` with the same runs, hence still ε-computing `f`. Step 3: the
Newman protocol `q` built from `pfm` is a private-coin finite-message protocol that
`(c · ε)`-computes `f` (`newmanProtocol_ApproxComputes`); since `c · ε < ε'`, the
private-coin complexity at error `ε'` is at most the complexity of `q`. Step 4: the
complexity of `q` is `⌈log₂ t⌉` plus the complexity of `pfm`, which equals that of `p`
and is at most `n`; assemble the chain of inequalities. -/
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
  -- Step 1: match on the public-coin complexity
  match h : PublicCoin.communicationComplexity f ε with
  | ⊤ => simp
  | (n : ℕ) =>
    -- There exists a public-coin protocol with complexity ≤ n
    obtain ⟨m, p, hp, hc_le⟩ :=
      (PublicCoin.communicationComplexity_le_iff f ε n).mp (le_of_eq h)
    -- Step 2: lift to FiniteMessage
    let pfm := PublicCoin.FiniteMessage.Protocol.ofProtocol p
    have hpfm_approx : pfm.ApproxComputes f ε := by
      intro x y
      simp only [pfm, PublicCoin.FiniteMessage.Protocol.rrun,
        Deterministic.FiniteMessage.Protocol.ofProtocol_run]
      exact hp x y
    -- Step 3: apply newmanProtocol: get a private-coin FM protocol that (c*ε)-computes f
    let q := pfm.newmanProtocol f ε c hc hpfm_approx
    have hq_approx :=
      FiniteMessage.Protocol.newmanProtocol_ApproxComputes
        pfm f ε c hc hpfm_approx
    -- q (c*ε)-computes f with c*ε < ε', so we can use
    -- communicationComplexity_le_of_finiteMessage
    have hbound :=
      PrivateCoin.communicationComplexity_le_of_finiteMessage
        f ε' (c * ε) hε' q hq_approx
    -- Step 4: bound q.complexity and assemble the chain
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
