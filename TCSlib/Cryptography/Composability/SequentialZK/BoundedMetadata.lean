/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite bounded phase-reduction metadata

The phase reduction's common input, verifier auxiliary word, verifier tape, phase index,
and raw encoded prefix range over an explicit finite nonempty product. Exact-length Boolean
vectors represent the fixed-size fields, and dependent pairs retain the precise lengths of
bounded fields. There is no witness or output test in this metadata. [PS10, Theorem 175.1].

## Main definitions

* `PhaseMetadata n a v q h`: finite metadata with the five prescribed length/index bounds.
* `PhaseMetadata.toData`: the raw reduction-advice word represented by this metadata.

## Main results

* `PhaseMetadata.word_lengths`: all five component bounds.
* `PhaseMetadata.toData_length_le`: packed advice has at most `2n+2a+2v+2q+h+8` bits.
* `PhaseMetadata.cover`: every tuple satisfying the five bounds is represented exactly.
* `PhaseMetadata.cover_data`: every bounded raw advice word equals some `m.toData`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

/-- `PhaseMetadata n a v q h` is a common input of exactly `n` bits, auxiliary word of at
most `a` bits, verifier tape of exactly `v` bits, phase index at most `q`, and raw prefix word
of at most `h` bits. Standard product, function and sigma instances make this type finite.
[PS10, Theorem 175.1, bounded phase-reduction advice].
`PhaseMetadata n a v q h = ((Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool))`. -/
abbrev PhaseMetadata (n a v q h : ℕ) : Type :=
  (Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
    Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool)

/-- The metadata type is
`(Fin n → Bool) × (Σ l : Fin (a+1), Fin l → Bool) × (Fin v → Bool) ×
 Fin (q+1) × (Σ l : Fin (h+1), Fin l → Bool)`. -/
theorem PhaseMetadata_eq (n a v q h : ℕ) : PhaseMetadata n a v q h =
    ((Fin n → Bool) × (Σ l : Fin (a + 1), Fin l → Bool) × (Fin v → Bool) ×
      Fin (q + 1) × (Σ l : Fin (h + 1), Fin l → Bool)) := rfl

namespace PhaseMetadata

/-- The all-false fixed-size words, empty bounded words and phase zero inhabit
`PhaseMetadata n a v q h`, including when any or all bounds vanish.
`Nonempty (PhaseMetadata n a v q h)`. -/
instance {n a v q h : ℕ} : Nonempty (PhaseMetadata n a v q h) :=
  ⟨(fun _ => false, ⟨⟨0, Nat.zero_lt_succ a⟩, Fin.elim0⟩, fun _ => false,
    ⟨0, Nat.zero_lt_succ q⟩, ⟨⟨0, Nat.zero_lt_succ h⟩, Fin.elim0⟩)⟩

/-- For metadata `m`, its raw advice is
`reductionData (ofFn m.1) (ofFn m.2.1.2) (ofFn m.2.2.1) m.2.2.2.1
  (ofFn m.2.2.2.2.2)`. [PS10, Theorem 175.1, phase-reduction advice].
`m.toData = reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1) m.2.2.2.1
(List.ofFn m.2.2.2.2.2)`. -/
def toData {n a v q h : ℕ} (m : PhaseMetadata n a v q h) : List Bool :=
  reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1) m.2.2.2.1
    (List.ofFn m.2.2.2.2.2)

/-- The packed metadata equation is `m.toData =
reductionData (ofFn m.1) (ofFn m.2.1.2) (ofFn m.2.2.1) m.2.2.2.1
  (ofFn m.2.2.2.2.2)`. -/
theorem toData_eq {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
    m.toData = reductionData (List.ofFn m.1) (List.ofFn m.2.1.2) (List.ofFn m.2.2.1)
      m.2.2.2.1 (List.ofFn m.2.2.2.2.2) := rfl

/-- For metadata `m`, its common-input and verifier-tape word lengths are exactly `n,v`,
its auxiliary and prefix word lengths are at most `a,h`, and its phase index is at most `q`.
`(List.ofFn m.1).length = n ∧ (List.ofFn m.2.1.2).length ≤ a ∧ (List.ofFn m.2.2.1).length = v ∧
(m.2.2.2.1 : ℕ) ≤ q ∧ (List.ofFn m.2.2.2.2.2).length ≤ h`.
-/
theorem word_lengths {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
    (List.ofFn m.1).length = n ∧ (List.ofFn m.2.1.2).length ≤ a ∧
    (List.ofFn m.2.2.1).length = v ∧ (m.2.2.2.1 : ℕ) ≤ q ∧
    (List.ofFn m.2.2.2.2.2).length ≤ h := by
  simp only [List.length_ofFn]
  exact ⟨True.intro, Nat.le_of_lt_succ m.2.1.1.isLt, True.intro,
    Nat.le_of_lt_succ m.2.2.2.1.isLt, Nat.le_of_lt_succ m.2.2.2.2.1.isLt⟩

/-- For metadata `m : PhaseMetadata n a v q h`,
`m.toData.length ≤ 2*n + 2*a + 2*v + 2*q + h + 8`.
[PS10, Theorem 175.1, polynomial phase-reduction advice bound]. -/
theorem toData_length_le {n a v q h : ℕ} (m : PhaseMetadata n a v q h) :
    m.toData.length ≤ 2 * n + 2 * a + 2 * v + 2 * q + h + 8 := by
  obtain ⟨hx, hz, hrV, hj, hpre⟩ := m.word_lengths
  rw [toData_eq, reductionData_length]
  omega

/-- For `x,z,rV,j,preWord` with `|x|=n`, `|z|≤a`, `|rV|=v`, `j≤q`, `|preWord|≤h`,
there is metadata `m : PhaseMetadata n a v q h` whose five represented components are
exactly `x,z,rV,j,preWord`. [PS10, Theorem 175.1, exact finite advice coverage].

**Proof sketch.** Use each bounded word's actual length as its sigma index and its padded
Boolean vector as its value. Fixed-size words use the given exact length. The public
`ofFn_padFin_of_length` equation recovers each original word without changing any bits;
the phase field stores the supplied bounded index directly. -/
theorem cover {n a v q h : ℕ} (x z rV : List Bool) (j : ℕ) (preWord : List Bool)
    (hx : x.length = n) (hz : z.length ≤ a) (hrV : rV.length = v)
    (hj : j ≤ q) (hpre : preWord.length ≤ h) :
    ∃ m : PhaseMetadata n a v q h,
      List.ofFn m.1 = x ∧ List.ofFn m.2.1.2 = z ∧ List.ofFn m.2.2.1 = rV ∧
      (m.2.2.2.1 : ℕ) = j ∧ List.ofFn m.2.2.2.2.2 = preWord := by
  let m : PhaseMetadata n a v q h :=
    (padFin n x, ⟨⟨z.length, Nat.lt_succ_of_le hz⟩, padFin z.length z⟩,
      padFin v rV, ⟨j, Nat.lt_succ_of_le hj⟩,
      ⟨⟨preWord.length, Nat.lt_succ_of_le hpre⟩, padFin preWord.length preWord⟩)
  refine ⟨m, ?_, ?_, ?_, rfl, ?_⟩
  · exact ofFn_padFin_of_length hx
  · exact ofFn_padFin_of_length rfl
  · exact ofFn_padFin_of_length hrV
  · exact ofFn_padFin_of_length rfl

/-- For `x,z,rV,j,preWord` with `|x|=n`, `|z|≤a`, `|rV|=v`, `j≤q`, `|preWord|≤h`,
there is `m : PhaseMetadata n a v q h` with
`m.toData = reductionData x z rV j preWord`. -/
theorem cover_data {n a v q h : ℕ} (x z rV : List Bool) (j : ℕ) (preWord : List Bool)
    (hx : x.length = n) (hz : z.length ≤ a) (hrV : rV.length = v)
    (hj : j ≤ q) (hpre : preWord.length ≤ h) :
    ∃ m : PhaseMetadata n a v q h, m.toData = reductionData x z rV j preWord := by
  obtain ⟨m, hx', hz', hrV', hj', hpre'⟩ := cover x z rV j preWord hx hz hrV hj hpre
  refine ⟨m, ?_⟩
  rw [toData_eq, hx', hz', hrV', hj', hpre']

end PhaseMetadata

end TCSlib.Cryptography.SequentialZK
