/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedSlices
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Precomputed messages and reconstruction records for selected rows

The fixed argument keys, output key and opposite nonce determine the challenge messages
and reconstruction records. No selected key or challenge nonce is used to compute them.
For at most two argument keys, the row uses the inner slice unless position zero of a
two-key row is selected; that case uses the outer slice and a precomputed inner ciphertext.

## Main definitions

* `SelectedRows.offset`, `length`: the selected encryption layer's slice shape.
* `SelectedRows.word`, `message`: the deterministic precomputed challenge plaintext.
* `SelectedRows.descriptor`: direct reading or known-key wrapping of a challenge slot.

## Main results

* The exact message length and typed-message encoding.
* Pointwise reconstruction of all selected positions in one- and two-key rows.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7, Algorithm 157.2.
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows

open Complexity Turing TCSlib.Cryptography

/-- The selected slice begins at `2n` for position zero in a two-key row, and at zero
for every other selected position. -/
def offset (n : ℕ) (ks : List (Fin n → Bool)) (p : ℕ) : ℕ :=
  if ks.length = 2 ∧ p = 0 then n + n else 0

/-- `offset n ks p` is `2n` in the outer-layer case and zero otherwise. -/
theorem offset_eq (n : ℕ) (ks : List (Fin n → Bool)) (p : ℕ) :
    offset n ks p = if ks.length = 2 ∧ p = 0 then n + n else 0 := rfl

/-- The selected plaintext length is `4n+2` for an outer-layer occurrence, and `n` otherwise. -/
def length (n : ℕ) (ks : List (Fin n → Bool)) (p : ℕ) : ℕ :=
  if ks.length = 2 ∧ p = 0 then 4 * n + 2 else n

/-- `length n ks p` is `4n+2` in the outer-layer case and `n` otherwise. -/
theorem length_eq (n : ℕ) (ks : List (Fin n → Bool)) (p : ℕ) :
    length n ks p = if ks.length = 2 ∧ p = 0 then 4 * n + 2 else n := rfl

/-- The precomputed plaintext is an inner encryption under the known second key for an
outer-layer occurrence, and the output-key word for an only-key or inner occurrence. -/
def word (E₁ : List Bool → List Bool) (n : ℕ) (ks : List (Fin n → Bool))
    (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) : List Bool :=
  if ks.length = 2 ∧ p = 0 then
    spEncStr E₁ (List.ofFn (ks.getD 1 default)) (List.ofFn o) (List.ofFn nonce.2)
  else List.ofFn o

/-- `word` selects the precomputed inner ciphertext or the output-key word by layer. -/
theorem word_eq (E₁ : List Bool → List Bool) (n : ℕ) (ks : List (Fin n → Bool))
    (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) :
    word E₁ n ks o nonce p = if ks.length = 2 ∧ p = 0 then
      spEncStr E₁ (List.ofFn (ks.getD 1 default)) (List.ofFn o) (List.ofFn nonce.2)
    else List.ofFn o := rfl

/-- The typed challenge message is the fixed-width padded view of the precomputed word. -/
def message (E₁ : List Bool → List Bool) (n : ℕ) (ks : List (Fin n → Bool))
    (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) :
    Fin (length n ks p) → Bool :=
  padFin (length n ks p) (word E₁ n ks o nonce p)

/-- `message` is `padFin (length n ks p) (word E₁ n ks o nonce p)`. -/
theorem message_eq (E₁ : List Bool → List Bool) (n : ℕ) (ks : List (Fin n → Bool))
    (o : Fin n → Bool) (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) :
    message E₁ n ks o nonce p =
      padFin (length n ks p) (word E₁ n ks o nonce p) := rfl

/-- Read challenge slot `j` directly, except at position one of a two-key row, where its
ciphertext is wrapped under the known first key and fixed outer nonce. -/
def descriptor (n : ℕ) (ks : List (Fin n → Bool))
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p j : ℕ) : List Bool :=
  if ks.length = 2 ∧ p = 1 then SliceReconstruction.wrappedRecord j
    (List.ofFn (ks.getD 0 default)) (List.ofFn nonce.1)
  else SliceReconstruction.directRecord j

/-- `descriptor` is a known-key wrapped record at the second position of a two-key row,
and a direct challenge record at all other selected positions. -/
theorem descriptor_eq (n : ℕ) (ks : List (Fin n → Bool))
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p j : ℕ) :
    descriptor n ks nonce p j = if ks.length = 2 ∧ p = 1 then
      SliceReconstruction.wrappedRecord j (List.ofFn (ks.getD 0 default)) (List.ofFn nonce.1)
    else SliceReconstruction.directRecord j := rfl

/-- The deterministic precomputed word has exactly the selected slice's message length,
provided `E₁` evaluates its prescribed `2n`-bit pad family. -/
theorem word_length
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x)) (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool)
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) :
    (word E₁ n ks o nonce p).length = length n ks p := by
  rw [word_eq, length_eq]
  split_ifs
  · exact SelectedSlices.innerCipher_length hGE₁ n _ o nonce.2
  · exact List.length_ofFn

/-- The typed message encodes exactly the precomputed word when `E₁` evaluates the pad
family. Padding has no effect because the word already has the prescribed length.

**Proof sketch.** The public vector-encoding reader converts padding to list padding. The
word-length identity identifies the requested width with the actual word length, so taking
that prefix of the word followed by padding returns the word itself. -/
theorem message_ofFn
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x)) (n : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool)
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) :
    List.ofFn (message E₁ n ks o nonce p) = word E₁ n ks o nonce p := by
  rw [message_eq, EnsembleLemmas.ofFn_padFin_eq_padL, EnsembleLemmas.padL_eq,
    ← word_length hGE₁ n ks o nonce p, List.take_left]

section Joint

variable {L L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hG hGE₁ hGE₂ in
/-- A selected row reconstructed from its slice-sampler slot is exactly the row with that
argument key and its encryption nonce replaced by the sampled key and nonce. The other
key and opposite nonce remain fixed. This holds for every sampler seed, for every valid
position in a row of at most two keys. [PS10, Theorem 163.7]

**Proof sketch.** A selected position excludes the zero-key case. With one key, position
zero reads the inner slice directly. With two keys, position zero reads the outer slice
whose message is the precomputed inner ciphertext; position one wraps the inner slice
under the known outer key. The three slice identities give the complete nested encryption.
List-update readers identify its argument keys, and the selected position identifies the
nonce half. No comparison between actual key values is used. -/
theorem reconstruct (n q : ℕ) (ks : List (Fin n → Bool)) (o : Fin n → Bool)
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p : ℕ) (j : Fin (q + 1))
    (hks : ks.length ≤ 2) (hp : p < ks.length)
    (offsets lens : Fin (q + 1) → ℕ) (msgs : ∀ i, Fin (lens i) → Bool)
    (hOff : offsets j = offset n ks p) (hMsg : List.ofFn (msgs j) = word E₁ n ks o nonce p)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.row E₂ (pairEncode (sliceMultiEncDist G n q offsets lens msgs (k, rs))
      (descriptor n ks nonce p j.val)) =
        (nestedSpecial E₁ E₂ n).enc (ks.set p k) o
          (if p = 0 then (rs j, nonce.2) else (nonce.1, rs j)) := by
  cases ks with
  | nil => simp only [List.length_nil] at hp; omega
  | cons k₀ rest =>
    cases rest with
    | nil =>
      have hp₀ : p = 0 := by simp only [List.length_cons, List.length_nil] at hp; omega
      subst p
      have hd : ¬ ([k₀].length = 2 ∧ (0 : ℕ) = 1) := by
          simp only [List.length_cons, List.length_nil]; omega
      have ho : ¬ ([k₀].length = 2 ∧ (0 : ℕ) = 0) := by
          simp only [List.length_cons, List.length_nil]; omega
      rw [descriptor_eq, if_neg hd, SelectedSlices.direct_sampler, hOff, hMsg, offset_eq,
        if_neg ho, word_eq, if_neg ho, List.set_cons_zero, if_pos rfl]
      exact SelectedSlices.only_row G G₁ G₂ E₁ E₂ hG hGE₁ n k o (rs j) nonce.2
    | cons k₁ tail =>
      have htail : tail = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hks; omega)
      subst tail
      have hp₂ : p = 0 ∨ p = 1 := by
        simp only [List.length_cons, List.length_nil] at hp; omega
      rcases hp₂ with rfl | rfl
      · have hd : ¬ ([k₀, k₁].length = 2 ∧ (0 : ℕ) = 1) := by
          simp only [List.length_cons, List.length_nil]; omega
        have ho : [k₀, k₁].length = 2 ∧ (0 : ℕ) = 0 := ⟨rfl, rfl⟩
        rw [descriptor_eq, if_neg hd, SelectedSlices.direct_sampler, hOff, hMsg, offset_eq,
          if_pos ho, word_eq, if_pos ho, List.getD_cons_succ, List.getD_cons_zero,
          List.set_cons_zero, if_pos rfl]
        exact SelectedSlices.outer_row G G₁ G₂ E₁ E₂ hG hGE₂ n k k₁ o (rs j) nonce.2
      · have hd : [k₀, k₁].length = 2 ∧ (1 : ℕ) = 1 := ⟨rfl, rfl⟩
        have ho : ¬ ([k₀, k₁].length = 2 ∧ (1 : ℕ) = 0) := by
          simp only [List.length_cons, List.length_nil]; omega
        rw [descriptor_eq, if_pos hd, SelectedSlices.wrapped_sampler, hOff, hMsg, offset_eq,
          if_neg ho, word_eq, if_neg ho, List.getD_cons_zero, List.set_cons_succ,
          List.set_cons_zero, if_neg (by decide : ¬ ((1 : ℕ) = 0))]
        exact SelectedSlices.inner_row G G₁ G₂ E₁ E₂ hG hGE₁ n k k₀ o nonce.1 (rs j)

end Joint

/-- A selected-row reconstruction record using a slot index `j≤q` has at most
`2q+3n+8` bits, uniformly in the fixed keys and nonce values. -/
theorem descriptor_length_le (n q : ℕ) (ks : List (Fin n → Bool))
    (nonce : (Fin n → Bool) × (Fin n → Bool)) (p j : ℕ) (hj : j ≤ q) :
    (descriptor n ks nonce p j).length ≤ 2 * q + 3 * n + 8 := by
  rw [descriptor_eq]
  split_ifs
  · rw [(SliceReconstruction.record_lengths [] j _ _).2.2, List.length_ofFn,
      List.length_ofFn]
    omega
  · rw [(SliceReconstruction.record_lengths [] j [] []).2.1]
    omega

/-- Every selected-row slice fits in the joint pad of length `2n+(n+(4n+2))`, regardless
of the row's fixed data. -/
theorem fits (n : ℕ) (ks : List (Fin n → Bool)) (p : ℕ) :
    offset n ks p + n + length n ks p ≤ (n + n) + (n + (4 * n + 2)) := by
  rw [offset_eq, length_eq]
  split_ifs
  · exact (SelectedSlices.slice_shapes_fit n).2
  · exact (SelectedSlices.slice_shapes_fit n).1

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedRows
