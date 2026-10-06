/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.PolyHierarchy.Defs
import TCSlib.Complexity.PolyHierarchy.Padding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Normalizing quantifier prefixes

The quantifier manipulations in [AB09, proof of Theorem 5.4] produce prefixes whose block
lengths are polynomial in `|x|` but not of the normal form `C · (|x| + 1)^c` of
`Complexity.SigmaP`, whose first block may have a different length from the others, and
whose verifier reads a polynomial-time transform of the tuple. This file proves that all
such prefixes still define `altClass b i` languages (`mem_altClass_of_normal`): pad every
block to a common normal-form length `B ≥` all original lengths `+ 1`, and let the new
verifier un-pad each block (`Complexity.PolyHierarchy.padDecode`, which is total and
surjective, hence transfers `∃` and `∀` alike) before running the old one.

## Main definitions

* `Complexity.PolyHierarchy.Extends` — `z` extends the tuple `w` by `k` blocks.

## Main results

* `Complexity.PolyHierarchy.qStep_transfer` — a total, surjective block decoder
  transfers one quantifier block.
* `Complexity.PolyHierarchy.altQuant_transfer` — the same for a whole prefix.
* `Complexity.PolyHierarchy.mem_altClass_of_normal` — a prefix with first-block length
  `ℓ₁(y)`, later block lengths `ℓ₂(y)` and verifier input `f(⟨y, u₁⟩, …)` defines an
  `altClass b (i+1)` language.
* `Complexity.PolyHierarchy.mem_altClass_of_uniform` — the uniform-length version.
* `Complexity.PolyHierarchy.preimage_mem_altClass` — `altClass b i` is closed under
  polynomial-time preimages.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2, Definition 5.3 and Theorem 5.4.)
-/

namespace Complexity.PolyHierarchy

open Turing Complexity

/-- `Extends k w z`: the tuple `z` is `⟨⋯⟨w, v₁⟩, …, v_k⟩` for some blocks `v₁, …, v_k`. -/
def Extends : ℕ → List Bool → List Bool → Prop
  | 0, w, z => z = w
  | k + 1, w, z => ∃ v : List Bool, Extends k (pairEncode w v) z

/-- The prefix of depth `k` of an extension by `k` blocks is recovered by `k` first
projections. -/
theorem Extends.iterate_pairFstD : ∀ {k : ℕ} {w z : List Bool}, Extends k w z →
    pairFstD^[k] z = w
  | 0, _, _, h => by simpa [Extends] using h
  | k + 1, w, z, ⟨v, h⟩ => by
    rw [Function.iterate_succ_apply', Extends.iterate_pairFstD h, pairFstD_pairEncode]

/-- **Transferring one block.** If `dec` maps the words of length `B` onto the words of
length `m` (and into them), and `Q'` on a length-`B` word agrees with `Q` on its decoding,
then the block `qStep b B Q'` is equivalent to `qStep b m Q`, for either quantifier. -/
theorem qStep_transfer {b : Bool} {B m : ℕ} {Q' Q : List Bool → Prop}
    (dec : List Bool → List Bool) (hlen : ∀ v, v.length = B → (dec v).length = m)
    (hsurj : ∀ u, u.length = m → ∃ v, v.length = B ∧ dec v = u)
    (h : ∀ v, v.length = B → (Q' v ↔ Q (dec v))) : qStep b B Q' ↔ qStep b m Q := by
  cases b with
  | true =>
    constructor
    · rintro ⟨v, hv, hq⟩
      exact ⟨dec v, hlen v hv, (h v hv).1 hq⟩
    · rintro ⟨u, hu, hq⟩
      obtain ⟨v, hv, rfl⟩ := hsurj u hu
      exact ⟨v, hv, (h v hv).2 hq⟩
  | false =>
    constructor
    · intro H u hu
      obtain ⟨v, hv, rfl⟩ := hsurj u hu
      exact (h v hv).1 (H v hv)
    · intro H v hv
      exact (h v hv).2 (H _ (hlen v hv))

/-- **Transferring a whole prefix.** Let `dec` map length-`B` words onto length-`m` words,
and let `F n` be a tuple map that decodes one more block at each depth:
`F (n+1) ⟨w, v⟩ = ⟨F n w, dec v⟩`. If on every `k`-block extension `z` of `w` the new
verifier `V'` agrees with the old verifier `V` after `F (n+k)`, then the `k`-block prefix
over `V'` with block length `B` at `w` is equivalent to the `k`-block prefix over `V`
with block length `m` at `F n w`.

**Proof sketch.** Induction on `k`; at each block apply `qStep_transfer` with `dec`, and
use the decoding equation of `F` to move the decoded block inside. -/
theorem altQuant_transfer (V V' : Language Bool) (B m : ℕ) (dec : List Bool → List Bool)
    (hlen : ∀ v, v.length = B → (dec v).length = m)
    (hsurj : ∀ u, u.length = m → ∃ v, v.length = B ∧ dec v = u)
    (F : ℕ → List Bool → List Bool)
    (hF : ∀ n w v, F (n + 1) (pairEncode w v) = pairEncode (F n w) (dec v)) :
    ∀ (k : ℕ) (b : Bool) (n : ℕ) (w : List Bool),
      (∀ z, Extends k w z → (z ∈ V' ↔ F (n + k) z ∈ V)) →
      (altQuant V' B b k w ↔ altQuant V m b k (F n w)) := by
  intro k
  induction k with
  | zero =>
    intro b n w h
    exact h w rfl
  | succ k ih =>
    intro b n w h
    rw [altQuant_succ, altQuant_succ]
    apply qStep_transfer dec hlen hsurj
    intro v _
    rw [← hF]
    apply ih (!b) (n + 1) (pairEncode w v)
    intro z hz
    have := h z ⟨v, hz⟩
    rwa [show n + (k + 1) = n + 1 + k by omega] at this

/-! ### The normalization theorem -/

/-- Base decoder of `mem_altClass_of_normal`: on the depth-one prefix `⟨y, U⟩`, un-pad the
first block to the template `fst s` and apply `f`. -/
private def nBase (f : List Bool → List Bool) (s w : List Bool) : List Bool :=
  f (pairEncode (pairFstD w) (padDecode (pairFstD s) (pairSndD w)))

/-- Block decoder of `mem_altClass_of_normal`: un-pad to the template `snd s`. -/
private def nDec (s v : List Bool) : List Bool := padDecode (pairSndD s) v

/-- Side information of `mem_altClass_of_normal`: the two length templates `1^{ℓ₁ y}`,
`1^{ℓ₂ y}`. -/
private def nSide (ℓ₁ ℓ₂ : List Bool → ℕ) (y : List Bool) : List Bool :=
  pairEncode (List.replicate (ℓ₁ y) true) (List.replicate (ℓ₂ y) true)

/-- The full verifier-input transformation of `mem_altClass_of_normal`. -/
private def nMap (f : List Bool → List Bool) (ℓ₁ ℓ₂ : List Bool → ℕ) (i : ℕ)
    (z : List Bool) : List Bool :=
  tupleDecode (nBase f) nDec i (nSide ℓ₁ ℓ₂ (pairFstD^[i + 1] z)) z

/-- The verifier-input transformation `nMap f ℓ₁ ℓ₂ i` is polynomial-time computable.

**Proof sketch.** The map is the tuple decoder applied to the pair of its side
information and its input. The base step (applying `f` to the re-paired, un-padded
first block) and the block decoder (un-padding to a template) are compositions of the
polynomial-time pairing projections, pair encoding, pad decoding and `f`; the side
information is a pair of unary polynomial-time templates evaluated on an iterated first
projection. Closure of polynomial-time computability under composition, pairing and
the tuple decoder then gives the claim, up to a pointwise unfolding of definitions. -/
private theorem polyTimeComputable_nMap {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) {ℓ₁ ℓ₂ : List Bool → ℕ} (h₁ : UnaryPT ℓ₁) (h₂ : UnaryPT ℓ₂)
    (i : ℕ) : PolyTimeComputable (nMap f ℓ₁ ℓ₂ i) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hbase : PolyTimeComputable (fun p => nBase f (pairFstD p) (pairSndD p)) := by
    have h := hf.comp ((hF.comp hS).pairEncode
      (polyTimeComputable_padDecode.comp ((hF.comp hF).pairEncode (hS.comp hS))))
    convert h using 1
    funext p
    simp [nBase]
  have hdec : PolyTimeComputable (fun p => nDec (pairFstD p) (pairSndD p)) := by
    have h := polyTimeComputable_padDecode.comp ((hS.comp hF).pairEncode hS)
    convert h using 1
    funext p
    simp [nDec]
  have hside : PolyTimeComputable (nSide ℓ₁ ℓ₂) := h₁.pairEncode h₂
  have h := (polyTimeComputable_tupleDecode hbase hdec i).comp
    ((hside.comp (polyTimeComputable_iterate_pairFstD (i + 1))).pairEncode
      polyTimeComputable_id)
  convert h using 1
  funext z
  simp [nMap]

/-- **Normalization of a quantifier prefix.** Let `V ∈ P`, `f` polynomial-time, and
`ℓ₁, ℓ₂` unary polynomial-time length functions. Then the language of all `y` with

`Q₁ U (|U| = ℓ₁(y)) Q₂ u₂ ⋯ Q_{i+1} u_{i+1} (|u_j| = ℓ₂(y)),
  ⟨⋯⟨f ⟨y, U⟩, u₂⟩, …, u_{i+1}⟩ ∈ V`

(alternating quantifiers, `Q₁ = ∃` iff `b = true`) is in `altClass b (i + 1)`. This is
the padding step of [AB09, proof of Theorem 5.4]: the book silently re-pads certificates
whenever quantifier blocks are merged or replaced by an equal class.

**Proof sketch.** Choose a normal-form length `B(n) = (A₁ + A₂ + 1)(n+1)^{a₁+a₂}`
exceeding `ℓ₁(y)` and `ℓ₂(y)` (both are polynomially bounded). The new verifier receives
`⟨⋯⟨y, U'⟩, …, u'_{i+1}⟩` with all blocks of length `B`, recovers `y` by `i + 1` first
projections, computes the templates `1^{ℓ₁ y}`, `1^{ℓ₂ y}`, un-pads `U'` to length
`ℓ₁ y` and the later blocks to length `ℓ₂ y`, applies `f` at the root, and runs `V`
(polynomial-time by `tupleDecode`). Since un-padding is total and onto, the first block
transfers by `qStep_transfer` and the remaining `i` blocks by `altQuant_transfer`. -/
theorem mem_altClass_of_normal {b : Bool} {i : ℕ} {V : Language Bool} (hV : V ∈ P)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    {ℓ₁ ℓ₂ : List Bool → ℕ} (h₁ : UnaryPT ℓ₁) (h₂ : UnaryPT ℓ₂) :
    {y | qStep b (ℓ₁ y) fun U => altQuant V (ℓ₂ y) (!b) i (f (pairEncode y U))} ∈
      altClass b (i + 1) := by
  obtain ⟨A₁, a₁, hA₁⟩ := h₁.bound
  obtain ⟨A₂, a₂, hA₂⟩ := h₂.bound
  refine ⟨A₁ + A₂ + 1, a₁ + a₂, nMap f ℓ₁ ℓ₂ i ⁻¹' V,
    preimage_mem_P hV (polyTimeComputable_nMap hf h₁ h₂ i), fun y => ?_⟩
  set B := (A₁ + A₂ + 1) * (y.length + 1) ^ (a₁ + a₂) with hBdef
  -- Both original lengths fit strictly inside the normal-form length `B`.
  have hpos : 1 ≤ (y.length + 1) ^ (a₁ + a₂) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hp₁ : (y.length + 1) ^ a₁ ≤ (y.length + 1) ^ (a₁ + a₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
  have hp₂ : (y.length + 1) ^ a₂ ≤ (y.length + 1) ^ (a₁ + a₂) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
  have hexp : B = A₁ * (y.length + 1) ^ (a₁ + a₂) + A₂ * (y.length + 1) ^ (a₁ + a₂) +
      (y.length + 1) ^ (a₁ + a₂) := by rw [hBdef]; ring
  have hB₁ : ℓ₁ y < B := by
    have := hA₁ y
    have := Nat.mul_le_mul_left A₁ hp₁
    have := Nat.zero_le (A₂ * (y.length + 1) ^ (a₁ + a₂))
    omega
  have hB₂ : ℓ₂ y < B := by
    have := hA₂ y
    have := Nat.mul_le_mul_left A₂ hp₂
    have := Nat.zero_le (A₁ * (y.length + 1) ^ (a₁ + a₂))
    omega
  set s := nSide ℓ₁ ℓ₂ y with hs
  have hs₁ : (pairFstD s).length = ℓ₁ y := by simp [hs, nSide]
  have hs₂ : (pairSndD s).length = ℓ₂ y := by simp [hs, nSide]
  show _ ↔ altQuant _ B b (i + 1) y
  rw [altQuant_succ]
  symm
  -- The first block: un-pad to the template `1^{ℓ₁ y}`.
  apply qStep_transfer (padDecode (pairFstD s))
    (fun v _ => by simp [hs₁])
    (fun u hu => exists_padDecode_eq (hu.trans hs₁.symm) (hs₁ ▸ hB₁))
  intro U _
  -- The remaining `i` blocks: un-pad to the template `1^{ℓ₂ y}`.
  have key := altQuant_transfer V (nMap f ℓ₁ ℓ₂ i ⁻¹' V) B (ℓ₂ y) (nDec s)
    (fun v _ => by simp [nDec, hs₂])
    (fun u hu => exists_padDecode_eq (hu.trans hs₂.symm) (hs₂ ▸ hB₂))
    (fun n w => tupleDecode (nBase f) nDec n s w)
    (fun n w v => tupleDecode_succ_pairEncode _ _ n s w v)
    i (!b) 0 (pairEncode y U) (by
      intro z hz
      have hroot : pairFstD^[i + 1] z = y := by
        rw [Function.iterate_succ_apply', hz.iterate_pairFstD, pairFstD_pairEncode]
      show nMap f ℓ₁ ℓ₂ i z ∈ V ↔ _
      rw [nMap, hroot, Nat.zero_add])
  rw [key]
  simp [tupleDecode, nBase]

/-- **Normalization, uniform version.** If `V ∈ P`, `f` is polynomial-time and `ℓ` is a
unary polynomial-time length function, then `{y | altQuant V (ℓ y) b i (f y)}` is in
`altClass b i`: block lengths that are polynomial in the input, and a verifier reading a
polynomial-time transform of the root, do not enlarge the class.

**Proof sketch.** For `i = 0` this is closure of `P` under polynomial-time preimages. For
`i + 1`, unfold the first block and apply `mem_altClass_of_normal` with
`f' ⟨y, U⟩ = ⟨f y, U⟩` and `ℓ₁ = ℓ₂ = ℓ`. -/
theorem mem_altClass_of_uniform {b : Bool} {i : ℕ} {V : Language Bool} (hV : V ∈ P)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    {ℓ : List Bool → ℕ} (hℓ : UnaryPT ℓ) :
    {y | altQuant V (ℓ y) b i (f y)} ∈ altClass b i := by
  cases i with
  | zero =>
    rw [altClass_zero]
    exact preimage_mem_P hV hf
  | succ i =>
    have hf' : PolyTimeComputable (fun p => pairEncode (f (pairFstD p)) (pairSndD p)) :=
      (hf.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD
    convert mem_altClass_of_normal (b := b) (i := i) hV hf' hℓ hℓ using 1
    ext y
    simp [altQuant_succ]

/-- **Closure under polynomial-time preimages**: if `L ∈ altClass b i` and `f` is
polynomial-time computable then `f⁻¹(L) ∈ altClass b i` (so every level `Σᵢᵖ`, `Πᵢᵖ` is
closed under polynomial-time many-one reductions).

**Proof sketch.** `y ∈ f⁻¹(L) ↔ altQuant V (C (|f y| + 1)^c) b i (f y)`; the block length
`C (|f y| + 1)^c` is a unary polynomial-time length function, so
`mem_altClass_of_uniform` applies. -/
theorem preimage_mem_altClass {b : Bool} {i : ℕ} {L : Language Bool}
    (hL : L ∈ altClass b i) {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    f ⁻¹' L ∈ altClass b i := by
  obtain ⟨C, c, V, hV, hLx⟩ := hL
  convert mem_altClass_of_uniform (b := b) (i := i) hV hf (unaryPT_poly C c hf) using 1
  ext y
  exact hLx (f y)

end Complexity.PolyHierarchy
