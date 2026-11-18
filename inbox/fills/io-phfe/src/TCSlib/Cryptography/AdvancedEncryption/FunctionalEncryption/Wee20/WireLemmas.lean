/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
import TCSlib.Cryptography.Pairing.MatrixDH.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Length and faithfulness of Wee's source-group words

## Main definitions

No new encoder or other runtime definition is introduced.

## Main results

* Wire.groupMatrix_length and groupVector_length: exact public-width lengths.
* Wire.groupMatrix_injective and groupVector_injective: fixed-shape faithfulness.

## References

* [Wee20] H. Wee, Functional Encryption for Quadratic Functions from k-Lin, Revisited,
  TCC 2020; full version, ePrint 2020/1420, Sections 3.1 and 4.2.

These are technical interface adapters to the existing BilinearGroup.groupMatrixEnc
length and injectivity theorems; they introduce no serialization/counting construction.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire

open Complexity Turing TCSlib.Cryptography.Pairing

/-- A source-group matrix word contains exactly one public-width block for each entry,
including empty row or column sets. This transports the existing pairing serialization law.

**Proof sketch.** Read groupMatrix_eq, groupVector_eq and groupMatrixEnc_eq to identify
the words. Reuse BilinearGroup.length_groupMatrixEnc; do not recount flatten lengths. -/
theorem groupMatrix_length {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) pp.group.G) :
    (groupMatrix pp A).length = m * n * G.wG.eval κ := by
  simpa only [groupMatrix_eq, groupVector_eq, BilinearGroup.groupMatrixEnc_eq] using
    (pp.group.length_groupMatrixEnc A)

/-- Source-group matrix words distinguish all matrices of the fixed shape, including
empty shapes. This is the existing pairing matrix encoder's injectivity through Wire.

**Proof sketch.** Identify the two encoders using their published readers, then apply
BilinearGroup.groupMatrixEnc_injective. No new block-splitting proof is required. -/
theorem groupMatrix_injective {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {m n : ℕ} :
    Function.Injective (groupMatrix pp (m := m) (n := n)) := by
  intro A B h
  apply pp.group.groupMatrixEnc_injective
  simpa only [groupMatrix_eq, groupVector_eq, BilinearGroup.groupMatrixEnc_eq] using h

/-- A source-group vector word contains exactly one public-width block per coordinate,
including the empty vector. It is the one-row case of the existing matrix serialization.

**Proof sketch.** Regard the vector as a one-row matrix. Use groupVector_eq and the
pairing encoder's equation reader plus existing singleton-list equations, then reuse
BilinearGroup.length_groupMatrixEnc at one row. -/
theorem groupVector_length {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {n : ℕ}
    (v : Fin n → pp.group.G) :
    (groupVector pp v).length = n * G.wG.eval κ := by
  simpa only [groupVector_eq, BilinearGroup.groupMatrixEnc_eq, List.ofFn_const,
    List.replicate_one, List.flatten_singleton, Nat.one_mul] using
    (pp.group.length_groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => v j))

/-- Source-group vector words distinguish all vectors of the fixed dimension, including
zero coordinates. This specializes the existing matrix encoder's injectivity to one row.

**Proof sketch.** Identify each vector word with the pairing encoding of its one-row
matrix, apply BilinearGroup.groupMatrixEnc_injective, and read that row. Reuse the
existing singleton-list equations rather than re-splitting point blocks. -/
theorem groupVector_injective {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) {n : ℕ} :
    Function.Injective (groupVector pp (n := n)) := by
  intro v w h
  have hrow :
      pp.group.groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => v j) =
        pp.group.groupMatrixEnc (fun (_ : Fin 1) (j : Fin n) => w j) := ?_
  swap
  · simpa only [groupVector_eq, BilinearGroup.groupMatrixEnc_eq, List.ofFn_const,
      List.replicate_one, List.flatten_singleton] using h
  exact congrArg (fun M : Matrix (Fin 1) (Fin n) pp.group.G => M 0)
    (pp.group.groupMatrixEnc_injective hrow)

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
