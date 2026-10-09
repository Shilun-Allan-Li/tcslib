/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.CircuitComplexity.PPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adleman's theorem: BPP ⊆ P/poly

Arora–Barak's Theorem 7.17: every language decidable by a randomized
polynomial-time algorithm has polynomial-size circuits.  The proof is a
counting argument: after error reduction, so few random strings are bad for
any input that one string `r₀` is good for *all* inputs of a given length,
and hardwiring `r₀` turns the verifier into a circuit.

## Main definitions

* `Randomized.VerifierHasCircuits` — "each fixing of the random string turns
  the verifier into a polynomial-size circuit family", the certificate-view
  residue of "`M` is a polynomial-time TM" (see **Deviations**).

## Main results

* `Randomized.adleman` — [AB09, Thm 7.17].

## Deviations from the source

In [AB09] the verifier is a polynomial-time TM, and the hardwiring step
quotes the simulation of poly-time TMs by poly-size circuits
([AB09, Thm 6.6], `P ⊆ P/poly`).  At this file's abstract level that
simulation enters as the explicit hypothesis
`hCirc : … → VerifierHasCircuits M p` on the efficiency notion `E`; for the
polynomial-time instantiation it is dischargeable from the library's
`Complexity.P_subset_PPoly` tableau machinery (see
`Randomized.PolyTimeModel`).  Circuits are the fan-in-two
`BoolCircuit.DAGCircuit` model of `CircuitComplexity.PPoly`, and the
conclusion is `Language.InPPoly` [AB09, Def 6.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open BoolCircuit

variable (E : VerifierModel)

/-- The verifier `M` (with random strings of length `p n` on length-`n`
inputs) turns into polynomial-size circuits when its random string is fixed:
there are constants `a, k` such that for every `n` and every random string
`r` of length `p n`, some well-formed fan-in-two circuit of size at most
`a·(n+1)^k` computes `x ↦ M x r` on length-`n` inputs.  This is what the
polynomial-time simulation [AB09, Thm 6.6] provides for TM verifiers; note
the single size bound uniform in `r`, which the counting argument needs. -/
def VerifierHasCircuits (M : List Bool → List Bool → Bool) (p : ℕ → ℕ) :
    Prop :=
  ∃ a k : ℕ, ∀ (n : ℕ) (r : List Bool), r.length = p n →
    ∃ D : DAGCircuit n,
      D.IsWellFormed ∧ D.IsFaninTwo ∧ D.size ≤ a * (n + 1) ^ k ∧
      ∀ v : Fin n → Bool, D.eval v = M (List.ofFn v) r

/-- **Adleman's theorem: `BPP ⊆ P/poly`** ([AB09, Thm 7.17]).  Relative to
the efficiency notion `E`: if `L ∈ BPP` and `E`-verifiers have circuits when
their random string is fixed (`hCirc`, the residue of [AB09, Thm 6.6]), then
`L` has polynomial-size circuits.

**Proof sketch.** By error reduction ([AB09, Thm 7.10],
`bpp_error_reduction`) take a verifier `M` for `L` with error at most
`2^{-(n+2)}` on inputs of length `n`, using `m = p n` random bits.  Call `r`
*bad* for `x` if `M(x,r) ≠ L(x)`; for each `x` at most `2^m/2^{n+2}` strings
are bad, so at most `2^n · 2^m/2^{n+2} = 2^m/4 < 2^m` strings are bad for
*some* length-`n` input.  Hence some `r₀ ∈ {0,1}^m` is good for every
`x ∈ {0,1}^n`.  By `hCirc`, `x ↦ M x r₀` is computed by a circuit of size
polynomial in `n`, and that circuit decides `L` on length-`n` inputs; the
resulting `DAGCircuitFamily` (one good circuit per length, well-formed and
fan-in-two with the uniform size bound) witnesses `L.InSIZE (polyLen a k)`
and hence `L.InPPoly`. -/
theorem adleman (hMaj : ClosedUnderMajority E) {L : Language Bool}
    (hL : InBPP E L)
    (hCirc : ∀ M a k, E.Eff (boolVerifier M) →
      VerifierHasCircuits M (polyLen a k)) :
    L.InPPoly := by
  classical
  -- Amplify to error at most `2^{-(n+2)}` (error reduction at `d = 1`).
  obtain ⟨M, a, k, hM, hprop⟩ :=
    bpp_error_reduction E hMaj ((inBPPWeak_iff_inBPP E hMaj 0 L).mpr hL) 1
  -- At every length some random string is good for all inputs at once.
  have hgood : ∀ n : ℕ, ∃ r₀ : Fin (polyLen a k n) → Bool,
      ∀ v : Fin n → Bool,
        (List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r₀) = true) ∧
        (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r₀) = false) := by
    intro n
    by_contra hbad
    rw [not_exists] at hbad
    have hbad' : ∀ r₀ : Fin (polyLen a k n) → Bool, ∃ v : Fin n → Bool,
        ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r₀) = true) ∧
           (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r₀) = false)) :=
      fun r₀ => not_forall.mp (hbad r₀)
    -- each input's bad set has probability at most `2^{-(n+2)}`
    have hv : ∀ v : Fin n → Bool,
        randProb (polyLen a k n) (fun l =>
          ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
             (List.ofFn v ∉ L → M (List.ofFn v) l = false))) ≤
          (1/2 : ℚ) ^ (n + 2) := by
      intro v
      have hlen : (List.ofFn v).length = n := List.length_ofFn
      have hth := hprop (List.ofFn v)
      rw [hlen] at hth
      have hexp : (n + 1) ^ 1 + 1 = n + 2 := by ring
      by_cases hxL : List.ofFn v ∈ L
      · have h1 := hth.1 hxL
        rw [hexp] at h1
        have hcongr : randProb (polyLen a k n) (fun l =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) l = false))) =
            randProb (polyLen a k n)
              (fun l => ¬ (M (List.ofFn v) l = true)) :=
          randProb_congr fun r => by simp [hxL]
        rw [hcongr, randProb_not]
        linarith
      · have h1 := hth.2 hxL
        rw [hexp] at h1
        have hcongr : randProb (polyLen a k n) (fun l =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) l = false))) =
            randProb (polyLen a k n)
              (fun l => ¬ (M (List.ofFn v) l = false)) :=
          randProb_congr fun r => by simp [hxL]
        rw [hcongr, randProb_not]
        linarith
    -- turn the probabilities into cardinalities and union-bound
    set m := polyLen a k n with hm
    have hcardv : ∀ v : Fin n → Bool,
        ((Finset.univ.filter fun r : Fin m → Bool =>
          ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
             (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false))).card
          : ℚ) ≤ (1/2 : ℚ) ^ (n + 2) * 2 ^ m := by
      intro v
      have := hv v
      unfold randProb at this
      rw [div_le_iff₀ (by positivity)] at this
      exact this
    have hcover : (Finset.univ : Finset (Fin m → Bool)) ⊆
        Finset.univ.biUnion (fun v : Fin n → Bool =>
          Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false))) := by
      intro r _
      obtain ⟨v, hv'⟩ := hbad' r
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hv'⟩⟩
    have hcard : ((2 : ℚ)) ^ m ≤ (2 : ℚ) ^ n * ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) := by
      have h1 : (2 : ℕ) ^ m ≤ (Finset.univ.biUnion
          (fun v : Fin n → Bool =>
            Finset.univ.filter fun r : Fin m → Bool =>
              ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
                 (List.ofFn v ∉ L →
                   M (List.ofFn v) (List.ofFn r) = false)))).card := by
        rw [← card_univ_bitstrings m]
        exact Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le
        (s := (Finset.univ : Finset (Fin n → Bool)))
        (t := fun v : Fin n → Bool =>
          Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false)))
      have h3 : ((2 : ℚ)) ^ m ≤
          ∑ v : Fin n → Bool, ((Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L →
                 M (List.ofFn v) (List.ofFn r) = false))).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      calc ((2 : ℚ)) ^ m ≤ ∑ _v : Fin n → Bool,
            ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) :=
            le_trans h3 (Finset.sum_le_sum fun v _ => hcardv v)
        _ = (2 : ℚ) ^ n * ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) := by
            rw [Finset.sum_const, card_univ_bitstrings, nsmul_eq_mul]
            push_cast
            ring
    -- but `2^n · 2^{-(n+2)} = 1/4 < 1`
    have hq : (2 : ℚ) ^ n * (1/2 : ℚ) ^ (n + 2) = 1/4 := by
      rw [div_pow, one_pow, pow_add]
      field_simp
      ring
    nlinarith [pow_pos (by norm_num : (0:ℚ) < 2) m, hcard, hq]
  choose r₀ hr₀ using hgood
  obtain ⟨a', k', hC⟩ := hCirc M a k hM
  have hDn : ∀ n : ℕ, ∃ D : DAGCircuit n,
      D.IsWellFormed ∧ D.IsFaninTwo ∧ D.size ≤ a' * (n + 1) ^ k' ∧
      ∀ v : Fin n → Bool, D.eval v = M (List.ofFn v) (List.ofFn (r₀ n)) :=
    fun n => hC n (List.ofFn (r₀ n)) List.length_ofFn
  choose D hD using hDn
  refine ⟨a', k', ⟨D⟩, fun n => (hD n).2.1, fun n => (hD n).2.2.1, ?_⟩
  ext w
  rw [DAGCircuitFamily.mem_language_iff]
  have heval := (hD w.length).2.2.2 w.get
  rw [List.ofFn_get] at heval
  constructor
  · intro hacc
    by_contra hw
    have := (hr₀ w.length w.get).2
    rw [List.ofFn_get] at this
    rw [heval, this hw] at hacc
    exact absurd hacc (by simp)
  · intro hw
    have := (hr₀ w.length w.get).1
    rw [List.ofFn_get] at this
    rw [heval, this hw]

end Randomized
