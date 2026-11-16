/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leftover hashing of many independent columns under one public matrix

## Main definitions

* `hashColumns`: hash `N` independent binary columns with the same matrix, `A ↦ A R`.

## Main results

* `distAdv_hashColumns_uniform_le`: `(A, A R)` is within `N` times the single-column
  leftover-hash error of `(A, U)` with `U` uniform.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.2.1 (leftover hashing in Regev encryption) and Section 6.1.3
  ("`[Ā | ĀR]` is very close to uniformly distributed").
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2, Lemma 1 (`(A, R·A)` close to uniform).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

The bound is a column-by-column hybrid over the existing single-column
`distAdv_hash_uniform_le`. It is not a matrix leftover-hash lemma: the family `R ↦ A R` is not
universal on whole matrices, and no such claim is made. No SIS hardness is used.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.Cryptography.SIS (Parameters)

/-- Hash `N` binary columns with one matrix: column `j` of `hashColumns P N A R` is
`hash P A (R · j)`, so `hashColumns P N A R = A R` modulo `q` [Pei16, Section 6.1.3, `ĀR`]. -/
def hashColumns (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus) :=
  fun i j => hash P A (fun c => R c j) i

/-- Entry `(i,j)` of `hashColumns P N A R` is coordinate `i` of the hash of column `j`. -/
theorem hashColumns_apply (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) (i : Fin P.dimension) (j : Fin N) :
    hashColumns P N A R i j = hash P A (fun c => R c j) i := rfl

/-- `hashColumns` is matrix multiplication by the `{0,1}` lift of `R`.

**Proof sketch.** Entrywise: `hash_eq` and the `mulVec`/`mul` entry formulas are the same sum. -/
theorem hashColumns_eq_mul (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    hashColumns P N A R = A * Matrix.of fun c j => ((R c j).toNat : ZMod P.modulus) := by
  sorry

/-- **Column hybrid for leftover hashing** [GSW13, Section 3.2, Lemma 1, statistical half;
Pei16, Section 6.1.3]: any independently randomized test distinguishes `(A, A R)` from a
uniform `(A, U)`, for uniform `A` and uniform binary `R` with `N` columns, with advantage at
most `N` times the single-column error `½·√(q^{dimension}/2^{columns})`.

**Proof sketch.** Hybrid `H_j`: the first `j` columns of the second component are uniform and
the rest are hashes of independent binary columns; `H_0` is the real sampler and `H_N` the
ideal one (after relabelling seeds by `uprob_comp_equiv`). `abs_sub_le_sum_hybrids` bounds the
end-to-end gap by the sum of neighbouring gaps. The `j`-th gap equals the advantage, between
`(A, hash A r)` and `(A, u)`, of the test that plants its challenge column at `j`, samples the
other columns itself with coins carried in its own randomness, and runs `D`; this is
`distAdv_hash_uniform_le`. The reduction's coins are a product of finite nonempty types. -/
theorem distAdv_hashColumns_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (N : ℕ)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.columns) (Fin N) Bool => (r.1, hashColumns P N r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → _) D ≤
      N * ((1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns)) := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
