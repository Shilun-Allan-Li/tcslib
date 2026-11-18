/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic sparse matrix factorization

## Main definitions

* `sparseEntries` lists nonzero matrix positions in row-major order.
* `sparseFactor` places one nonzero entry in each factor slot, padding unused slots by zero.

## Main results

* `sparseFactor_mul` reconstructs a matrix with at most `t` nonzero entries.
* `sparseFactor_mul_of_card_le` reads the sparsity hypothesis as a finite cardinal bound.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, sampling algorithm 1SdSamp, p. 16.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviation.** The paper uses the existence of factors for a matrix with at most `t`
nonzero entries. We specify the factors deterministically: list positions in row-major
order, put the entry value in its row in a left column, and put one in its column in the
corresponding right row. This works over any semiring and uses no rank theory or
choice-based enumeration. These are raw deterministic functions; efficiency is a later
core-target obligation, not a theorem of this module.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

variable {rows cols : ℕ} {R : Type*} [Semiring R] [DecidableEq R]

/-- Nonzero positions are listed in row-major order,
`sparseEntries M = [(i,j) in Fin rows × Fin cols | M i j ≠ 0]`
[JLS26, sampling algorithm 1SdSamp, p. 16]. The order fixes the paper's unspecified factors;
`List.finRange` avoids a choice-based finite enumeration. -/
def sparseEntries (M : Matrix (Fin rows) (Fin cols) R) : List (Fin rows × Fin cols) :=
  ((List.finRange rows).flatMap (fun i => (List.finRange cols).map (fun j => (i, j)))).filter
    (fun c => decide (M c.1 c.2 ≠ 0))

/-- Sparse positions are the row-major list filtered by nonzero entries. Glue reader. -/
theorem sparseEntries_eq (M : Matrix (Fin rows) (Fin cols) R) :
    sparseEntries M =
      ((List.finRange rows).flatMap (fun i => (List.finRange cols).map (fun j => (i, j)))).filter
        (fun c => decide (M c.1 c.2 ≠ 0)) := rfl

/-- The left factor puts the `k`th nonzero entry in its row in column `k`,
with zero for missing slots [JLS26, sampling algorithm 1SdSamp, p. 16].
The row-major order makes the paper's factor choice deterministic. -/
def sparseLeft (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin rows) (Fin t) R :=
  fun i k => match (sparseEntries M)[k.val]? with
    | none => 0
    | some c => if i = c.1 then M c.1 c.2 else 0

/-- The left factor reads a nonzero position by its slot and writes its entry value. Glue reader. -/
theorem sparseLeft_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseLeft M t = fun i k => match (sparseEntries M)[k.val]? with
      | none => 0
      | some c => if i = c.1 then M c.1 c.2 else 0 := rfl

/-- The right factor puts one at the column of the `k`th nonzero entry in row `k`,
with zero for missing slots [JLS26, sampling algorithm 1SdSamp, p. 16].
The row-major order makes the paper's factor choice deterministic. -/
def sparseRight (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin t) (Fin cols) R :=
  fun k j => match (sparseEntries M)[k.val]? with
    | none => 0
    | some c => if j = c.2 then 1 else 0

/-- The right factor reads a nonzero position by its slot and selects its column. Glue reader. -/
theorem sparseRight_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseRight M t = fun k j => match (sparseEntries M)[k.val]? with
      | none => 0
      | some c => if j = c.2 then 1 else 0 := rfl

/-- Sparse factors are the deterministic pair `(sparseLeft M t, sparseRight M t)`
[JLS26, sampling algorithm 1SdSamp, p. 16]. No existence witness or rank decomposition
is selected; the raw functions are defined even when the sparsity bound fails. -/
def sparseFactor (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    Matrix (Fin rows) (Fin t) R × Matrix (Fin t) (Fin cols) R :=
  (sparseLeft M t, sparseRight M t)

/-- The sparse-factor pair consists of its explicit left and right factors. Glue reader. -/
theorem sparseFactor_eq (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    sparseFactor M t = (sparseLeft M t, sparseRight M t) := rfl

/-- The first sparse factor is the explicit left matrix. Glue projection reader. -/
theorem sparseFactor_fst (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    (sparseFactor M t).1 = sparseLeft M t := rfl

/-- The second sparse factor is the explicit right matrix. Glue projection reader. -/
theorem sparseFactor_snd (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ) :
    (sparseFactor M t).2 = sparseRight M t := rfl

/-- Nonzero positions occur exactly once in the sparse list
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue for the chosen factors.

**Proof sketch.** The row-major list is a product of duplicate-free finite ranges;
filtering preserves duplicate-freeness. -/
theorem sparseEntries_nodup (M : Matrix (Fin rows) (Fin cols) R) :
    (sparseEntries M).Nodup := by
  rw [sparseEntries_eq]
  exact ((List.nodup_finRange rows).product (List.nodup_finRange cols)).filter _

/-- A position belongs to the sparse list exactly when its entry is nonzero
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue.

**Proof sketch.** Every finite row and column occurs in `List.finRange`; use the filter test. -/
theorem mem_sparseEntries_iff (M : Matrix (Fin rows) (Fin cols) R)
    (c : Fin rows × Fin cols) : c ∈ sparseEntries M ↔ M c.1 c.2 ≠ 0 := by
  rw [sparseEntries_eq]
  change c ∈ ((List.finRange rows).product (List.finRange cols)).filter
    (fun p => decide (M p.1 p.2 ≠ 0)) ↔ M c.1 c.2 ≠ 0
  rcases c with ⟨i, j⟩
  have hmem : (i, j) ∈ (List.finRange rows).product (List.finRange cols) :=
    List.mem_product.mpr ⟨List.mem_finRange i, List.mem_finRange j⟩
  simp only [List.mem_filter, hmem, true_and, decide_eq_true_eq]

/-- The sparse list's length equals the number of nonzero matrix positions
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue.

**Proof sketch.** Use duplicate-freeness and `mem_sparseEntries_iff` to identify the finite set. -/
theorem sparseEntries_length_eq_card (M : Matrix (Fin rows) (Fin cols) R) :
    (sparseEntries M).length =
      (Finset.univ.filter (fun c : Fin rows × Fin cols => M c.1 c.2 ≠ 0)).card := by
  rw [← List.toFinset_card_of_nodup (sparseEntries_nodup M)]
  apply congrArg Finset.card
  ext c
  simp only [List.mem_toFinset, mem_sparseEntries_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- At most `t` nonzero entries suffice for the explicit factors to multiply to the matrix,
`(sparseFactor M t).1 * (sparseFactor M t).2 = M`
[JLS26, sampling algorithm 1SdSamp, p. 16]. This constructive factorization replaces the
paper's rank-existence justification without changing its factors' dimensions.

**Proof sketch.** Expand matrix multiplication. For each slot, the two factors produce
one entry at its unique row and column. Each nonzero entry has exactly one slot by
`sparseEntries_nodup`, and every slot beyond the list length contributes zero. -/
theorem sparseFactor_mul (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ)
    (h : (sparseEntries M).length ≤ t) :
    (sparseFactor M t).1 * (sparseFactor M t).2 = M := by
  rw [sparseFactor_fst, sparseFactor_snd]
  ext i j
  rw [Matrix.mul_apply, sparseLeft_eq, sparseRight_eq]
  by_cases hij : M i j = 0
  · -- Step 1: a zero target entry makes every slot's contribution zero.
    rw [hij]
    apply Finset.sum_eq_zero
    intro k _
    cases hk : (sparseEntries M)[k.val]? with
    | none => simp only [hk, zero_mul]
    | some c =>
      by_cases hi : i = c.1
      · by_cases hj : j = c.2
        · have hz : M c.1 c.2 = 0 := (congrArg₂ M hi.symm hj.symm).trans hij
          simp only [hk, if_pos hi, if_pos hj, hz, mul_one]
        · simp only [hk, if_pos hi, if_neg hj, mul_zero]
      · simp only [hk, if_neg hi, zero_mul]
  · -- Step 2: find the target nonzero entry's existing list slot.
    obtain ⟨q, hqlen, hq⟩ := List.mem_iff_getElem.mp
      ((mem_sparseEntries_iff M (i, j)).mpr hij)
    have hqopt : (sparseEntries M)[q]? = some (i, j) :=
      List.getElem?_eq_some_iff.mpr ⟨hqlen, hq⟩
    let q' : Fin t := ⟨q, Nat.lt_of_lt_of_le hqlen h⟩
    rw [Finset.sum_eq_single q']
    · -- Step 3: the selected slot contributes exactly the target entry.
      simp only [q', hqopt, if_true, mul_one]
    · -- Step 4: every other slot is padding or has a different row/column.
      intro k _ hneq
      cases hk : (sparseEntries M)[k.val]? with
      | none => simp only [hk, zero_mul]
      | some c =>
        by_cases hi : i = c.1
        · by_cases hj : j = c.2
          · have hc : c = (i, j) := Prod.ext hi.symm hj.symm
            have hqk : q = k.val :=
              List.getElem?_inj hqlen (sparseEntries_nodup M)
                (hqopt.trans (hk.trans (congrArg some hc)).symm)
            exact (hneq (Fin.ext hqk.symm)).elim
          · simp only [hk, if_pos hi, if_neg hj, mul_zero]
        · simp only [hk, if_neg hi, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_univ q')).elim

/-- A finite cardinal bound on nonzero entries implies reconstruction by the sparse factors
[JLS26, sampling algorithm 1SdSamp, p. 16]. This is mathematical glue for bucket matrices.

**Proof sketch.** Translate cardinality to sparse-list length, then use `sparseFactor_mul`. -/
theorem sparseFactor_mul_of_card_le (M : Matrix (Fin rows) (Fin cols) R) (t : ℕ)
    (h : (Finset.univ.filter (fun c : Fin rows × Fin cols => M c.1 c.2 ≠ 0)).card ≤ t) :
    (sparseFactor M t).1 * (sparseFactor M t).2 = M := by
  exact sparseFactor_mul M t ((sparseEntries_length_eq_card M).symm ▸ h)

end TCSlib.Cryptography.Obfuscation.StructuredSeed
